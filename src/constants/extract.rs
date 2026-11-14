//! Evaluates the client scripts and collects the constants.

use std::rc::Rc;

use unfuck::interp::BuiltinModule;
use unfuck::interp::HostAccess;
use unfuck::interp::ModuleCode;
use unfuck::interp::ModuleSource;
use unfuck::interp::Signal;
use unfuck::interp::Value;
use unfuck::interp::Vm;
use unfuck::interp::VmConfig;
use unfuck::interp::object::CallArgs;
use unfuck::interp::vm::ImportRecord;

use crate::constants::client;
use crate::constants::error::ConstantsError;
use crate::constants::executable::ClientExecutable;
use crate::constants::game::BuildNumber;
use crate::constants::game::ClientBuild;
use crate::constants::json::Converter;
use crate::constants::json::Json;
use crate::constants::json::JsonText;
use crate::constants::scripts::ScriptArchive;

/// The constants of one build, in `constants.json` key order.
#[derive(Debug, Clone, PartialEq)]
pub struct Constants {
    build: BuildNumber,
    json: Json,
}

impl Constants {
    /// Rejects constants whose `VERSION.BUILD` is not `build`, which means
    /// the scripts belong to another build.
    fn new(build: BuildNumber, json: Json) -> Result<Self, ConstantsError> {
        let reported = match json.get("VERSION").and_then(|version| version.get("BUILD")) {
            Some(Json::Integer(text)) => text.parse::<u32>().ok().map(BuildNumber::new),
            _ => None,
        };
        let Some(reported) = reported else {
            return Err(ConstantsError::MissingBuild { expected: build });
        };
        if reported != build {
            return Err(ConstantsError::BuildMismatch { expected: build, found: reported });
        }

        Ok(Self { build, json })
    }

    pub fn build(&self) -> BuildNumber {
        self.build
    }

    pub fn json(&self) -> &Json {
        &self.json
    }

    /// The `constants.json` text.
    pub fn render(&self) -> String {
        self.json.render()
    }
}

/// The outcome of evaluating one build's client scripts.
pub struct Extraction {
    pub constants: Result<Constants, ConstantsError>,
    /// Modules that were not found or whose body stopped early.
    pub incomplete_modules: Vec<ImportRecord>,
}

/// Evaluates the client scripts of `build` and reads every constant. The
/// interpreter never touches the host; `host_access` decides whether client
/// code that asks for host resources sees unknown results or refusals.
///
/// The outer error covers failures to start the interpreter. Failures while
/// reading constants are in [`Extraction::constants`], next to the modules
/// that explain them.
///
/// The interpreter recurses on the Rust stack once per Python call, so it
/// runs on a thread whose stack fits CPython's recursion limit.
pub fn extract(build: &ClientBuild, host_access: HostAccess) -> Result<Extraction, ConstantsError> {
    const STACK_BYTES: usize = 1 << 30;

    let build = build.clone();
    let worker = std::thread::Builder::new()
        .name("python".to_owned())
        .stack_size(STACK_BYTES)
        .spawn(move || -> Result<Extraction, ConstantsError> {
            let executable = build.executable().map(ClientExecutable::open).transpose()?;
            let extractor = Extractor::new(ScriptArchive::open(build.scripts())?, executable, host_access)?;
            let constants = extractor.run().and_then(|json| Constants::new(build.build(), json));

            Ok(Extraction { constants, incomplete_modules: extractor.incomplete_modules() })
        })
        .map_err(|source| ConstantsError::Thread { source })?;

    match worker.join() {
        Ok(result) => result,
        Err(panic) => std::panic::resume_unwind(panic),
    }
}

/// An interpreter loaded with one build's client scripts. It must run on a
/// thread with a large stack; see [`extract`].
struct Extractor {
    archive: Rc<ScriptArchive>,
    vm: Vm,
}

impl Extractor {
    /// `executable`, when given, decides which modules missing from the
    /// archive the client links in; the rest fail to import.
    fn new(
        archive: ScriptArchive,
        executable: Option<ClientExecutable>,
        host_access: HostAccess,
    ) -> Result<Self, ConstantsError> {
        let archive = Rc::new(archive);
        let mut config = VmConfig::windows_x64();
        config.host_access = host_access;
        if let Some(executable) = &executable {
            config.host = executable.host_facts();
        }

        let source = ArchiveSource { archive: Rc::clone(&archive), executable };
        let vm = Vm::new(config, Box::new(source))
            .map_err(|signal| ConstantsError::Bootstrap { detail: format!("{signal:?}") })?;
        client::register(&vm);

        Ok(Self { archive, vm })
    }

    /// Evaluates the client scripts and reads every constant. A module that
    /// failed to unpack takes precedence over any error it caused, since the
    /// interpreter saw that module as missing.
    fn run(&self) -> Result<Json, ConstantsError> {
        let constants = self.read_constants();

        if let Some(failure) = self.archive.take_failures().into_iter().next() {
            return Err(failure);
        }

        constants
    }

    fn read_constants(&self) -> Result<Json, ConstantsError> {
        let session = Session { vm: &self.vm };

        // The engine's own imports run first, in its order. Circular imports
        // between client modules only resolve when modules load in the
        // order the client loads them. Failures are recorded on the module
        // and surface only if a constant depends on it.
        for module in client::STARTUP_MODULES {
            let _ = self.vm.import_module(module).map_err(|signal| describe_signal(&self.vm, &signal));
        }

        let mut entries = Vec::new();
        for spec in KEYS {
            entries.push((JsonText::from(spec.name), (spec.read)(&session, spec.name)?));
        }
        for (name, global) in SHARED_INFO_KEYS {
            entries.push((JsonText::from(*name), read_shared_info(&session, name, global)?));
        }
        for name in BATTLE_RESULTS_KEYS {
            entries.push((JsonText::from(*name), session.json_at(name, "BattleResultsUtils", &[name])?));
        }

        Ok(Json::Object(entries))
    }

    /// Modules that were not found or whose body stopped early. Constants
    /// never depend on them silently: a value that needs them is unknown and
    /// fails extraction.
    fn incomplete_modules(&self) -> Vec<ImportRecord> {
        self.vm.import_records().into_iter().filter(|record| record.failure.is_some()).collect()
    }
}

struct ArchiveSource {
    archive: Rc<ScriptArchive>,
    executable: Option<ClientExecutable>,
}

impl ModuleSource for ArchiveSource {
    fn find(&self, name: &str) -> Option<ModuleCode> {
        self.archive.find(name)
    }

    /// Without the executable, every module missing from the archive is
    /// taken to be linked into the client.
    fn builtin(&self, name: &str) -> BuiltinModule {
        match &self.executable {
            Some(executable) if executable.links_module(name) => BuiltinModule::Present,
            Some(_) => BuiltinModule::Absent,
            None => BuiltinModule::Present,
        }
    }
}

pub(crate) fn describe_signal(vm: &Vm, signal: &Signal) -> String {
    let trace = vm.take_trace();
    let location = if trace.is_empty() { String::new() } else { format!(" (at {})", trace.join(" <- ")) };

    match signal {
        Signal::Raise(exception) => format!("{}{location}", vm.describe_exception(exception)),
        Signal::Halt(halt) => format!("{halt}{location}"),
    }
}

/// One output key: how to read it from the evaluated client.
struct KeySpec {
    name: &'static str,
    read: fn(&Session<'_>, &'static str) -> Result<Json, ConstantsError>,
}

/// Battle results layouts exported by `BattleResultsUtils`.
const BATTLE_RESULTS_KEYS: &[&str] = &[
    "CLIENT_BUILDING_INTERACTION_DETAILS",
    "CLIENT_PUBLIC_RESULTS",
    "CLIENT_PUBLIC_RESULTS_INDICES",
    "CLIENT_VEH_INTERACTION_DETAILS",
    "COMMON_ECONOMICS",
    "COMMON_ECONOMICS_INDICES",
    "COMMON_RESULTS",
    "INIT_ECONOMICS",
    "INIT_ECONOMICS_INDICES",
    "PLAYER_FULL_RESULTS",
    "PLAYER_PRIVATE_RESULTS",
    "PLAYER_PRIVATE_RESULTS_INDICES",
    "SUBTOTAL_ECONOMICS",
    "SUBTOTAL_ECONOMICS_INDICES",
];

/// Shared player info records, by output prefix and `PlayersInfo` global.
const SHARED_INFO_KEYS: &[(&str, &str)] = &[
    ("PLAYER_NUM_MEMBER_MAP", "gSharedPlayerInfo"),
    ("BOT_NUM_MEMBER_MAP", "gSharedBotInfo"),
    ("OBSERVER_NUM_MEMBER_MAP", "gSharedObserverInfo"),
];

/// The mods API package, whose submodules expose game enums to mods.
const MODS_API: &str = "ModsShell.API_v_1_0";

const KEYS: &[KeySpec] = &[
    KeySpec { name: "VERSION", read: read_version },
    KeySpec {
        name: "SHIP_TYPES",
        read: |session, key| session.json_at(key, "BattleItemDef", &["BuffItemInfo", "ShipTypes", "ID_BY_TYPE"]),
    },
    KeySpec {
        name: "CONSUMABLE_IDS",
        read: |session, key| session.json_at(key, "BattleItemDef", &["ConsumableItemInfo", "ConsumableIDsMap"]),
    },
    KeySpec { name: "RIBBONS", read: read_ribbons },
    KeySpec { name: "DAMAGE_STATS", read: read_damage_stats },
    KeySpec {
        name: "UNIT_TYPES",
        read: |session, key| session.json_at(key, "ShipConfigDescription", &["UNIT_TYPE_NAMES"]),
    },
    KeySpec {
        name: "SKILLS_BY_SHIP_TYPE",
        read: |session, key| session.json_at(key, "CommonCrewSkills", &["SKILLS_BY_SHIP_TYPE"]),
    },
    KeySpec {
        name: "GAME_MODES",
        read: |session, key| session.json_at(key, "BattleDefinitions", &["GameMode", "names"]),
    },
    KeySpec {
        name: "BATTLE_STAGES",
        read: |session, key| session.public_vars(key, "BattleDefinitions", &["BattleStage"]),
    },
    KeySpec { name: "FINISH_REASONS", read: read_finish_reasons },
    KeySpec {
        name: "SHARED_DATA_CONSTANTS",
        read: |session, key| session.public_vars(key, "SharedDataConstants", &["SharedDataConstants"]),
    },
    KeySpec { name: "DEATH_REASONS", read: read_death_reasons },
];

struct Session<'a> {
    vm: &'a Vm,
}

impl Session<'_> {
    fn failure(&self, key: &'static str, expression: &str, signal: Signal) -> ConstantsError {
        ConstantsError::Evaluation { key, expression: expression.to_owned(), detail: describe_signal(self.vm, &signal) }
    }

    fn module(&self, key: &'static str, name: &str) -> Result<Value, ConstantsError> {
        self.vm.import_module(name).map_err(|signal| self.failure(key, name, signal))
    }

    /// `module.a.b.c`.
    fn value_at(&self, key: &'static str, module: &str, path: &[&str]) -> Result<Value, ConstantsError> {
        let mut value = self.module(key, module)?;
        let mut expression = module.to_owned();

        for name in path {
            expression.push('.');
            expression.push_str(name);
            value = self.vm.getattr_str(&value, name).map_err(|signal| self.failure(key, &expression, signal))?;
        }

        Ok(value)
    }

    fn json(&self, key: &'static str, value: &Value, path: &str) -> Result<Json, ConstantsError> {
        Converter::new(self.vm, key).convert(value, path)
    }

    fn json_at(&self, key: &'static str, module: &str, path: &[&str]) -> Result<Json, ConstantsError> {
        let value = self.value_at(key, module, path)?;

        self.json(key, &value, &format!("{module}.{}", path.join(".")))
    }

    /// Entries of `vars(target)` whose names are not dunder names.
    fn vars(&self, key: &'static str, target: &Value, expression: &str) -> Result<Vec<(Value, Value)>, ConstantsError> {
        let dict = self.vm.getattr_str(target, "__dict__").map_err(|signal| self.failure(key, expression, signal))?;
        let Value::Object(dict) = &dict else {
            return Err(ConstantsError::Unserializable {
                key,
                path: format!("vars({expression})"),
                type_name: self.vm.type_name(&dict),
            });
        };

        let dict = match &dict.payload {
            unfuck::interp::value::Payload::DictProxy(inner) => Rc::clone(inner),
            _ => Rc::clone(dict),
        };

        self.vm.dict_items(&dict).map_err(|signal| self.failure(key, expression, signal))
    }

    fn public_vars(&self, key: &'static str, module: &str, path: &[&str]) -> Result<Json, ConstantsError> {
        let target = self.value_at(key, module, path)?;
        let expression = format!("{module}.{}", path.join("."));
        let entries: Vec<(Value, Value)> =
            self.vars(key, &target, &expression)?.into_iter().filter(|(name, _)| !is_dunder(self.vm, name)).collect();

        self.json(key, &self.dict_of(key, entries, &expression)?, &format!("vars({expression})"))
    }

    /// Builds an interpreter dict, so key order follows CPython's.
    fn dict_of(
        &self,
        key: &'static str,
        entries: Vec<(Value, Value)>,
        expression: &str,
    ) -> Result<Value, ConstantsError> {
        let dict = self.vm.new_dict();

        for (name, value) in entries {
            self.vm.dict_set(&dict, name, value).map_err(|signal| self.failure(key, expression, signal))?;
        }

        Ok(Value::Object(dict))
    }

    fn call(&self, key: &'static str, function: &Value, expression: &str) -> Result<Value, ConstantsError> {
        self.vm.call(function, CallArgs::default()).map_err(|signal| self.failure(key, expression, signal))
    }

    /// A submodule of the mods API package, as attribute access on the
    /// package sees it once the submodule is loaded.
    fn mods_api(&self, key: &'static str, submodule: &str) -> Result<Value, ConstantsError> {
        let package = self.module(key, MODS_API)?;
        let expression = format!("{MODS_API}.{submodule}");

        match self.vm.getattr_str(&package, submodule) {
            Ok(value) if !value.is_unknown() => Ok(value),
            _ => self.module(key, &expression),
        }
    }
}

fn is_dunder(vm: &Vm, name: &Value) -> bool {
    vm.text_of(name).is_some_and(|text| text.len() >= 4 && text.starts_with("__") && text.ends_with("__"))
}

fn read_version(session: &Session<'_>, key: &'static str) -> Result<Json, ConstantsError> {
    let mut entries = Vec::new();

    for name in ["BUILD", "VERSION", "PATCH"] {
        let value = session.value_at(key, "Version", &[name])?;
        entries.push((Value::str(name), value));
    }

    let dict = session.dict_of(key, entries, "Version")?;

    session.json(key, &dict, "Version")
}

fn read_ribbons(session: &Session<'_>, key: &'static str) -> Result<Json, ConstantsError> {
    let gate = session.mods_api(key, "constantsGate")?;
    let ribbons = session
        .vm
        .getattr_str(&gate, "RibbonsType")
        .map_err(|signal| session.failure(key, "constantsGate.RibbonsType", signal))?;
    let int_type = Value::Object(Rc::clone(&session.vm.types().int));

    let mut entries = Vec::new();
    for (name, value) in session.vars(key, &ribbons, "constantsGate.RibbonsType")? {
        let is_ribbon = session.vm.text_of(&name).is_some_and(|text| text.starts_with("RIBBON_"));
        let is_int = session
            .vm
            .isinstance(&value, &int_type)
            .map_err(|signal| session.failure(key, "constantsGate.RibbonsType", signal))?;
        if is_ribbon && is_int {
            entries.push((value, name));
        }
    }

    let dict = session.dict_of(key, entries, "constantsGate.RibbonsType")?;

    session.json(key, &dict, "constantsGate.RibbonsType")
}

fn read_damage_stats(session: &Session<'_>, key: &'static str) -> Result<Json, ConstantsError> {
    let stats = session.value_at(key, "Avatar", &["DamageStatsType"])?;
    let names = session
        .vm
        .attribute_names(&stats)
        .map_err(|signal| session.failure(key, "dir(Avatar.DamageStatsType)", signal))?;

    let mut entries = Vec::new();
    for name in names {
        let Some(text) = session.vm.text_of(&name) else {
            continue;
        };
        if !text.starts_with("DAMAGE_STATS_") {
            continue;
        }
        let value = session
            .vm
            .getattr_str(&stats, &text)
            .map_err(|signal| session.failure(key, &format!("Avatar.DamageStatsType.{text}"), signal))?;
        entries.push((name, value));
    }

    let dict = session.dict_of(key, entries, "Avatar.DamageStatsType")?;

    session.json(key, &dict, "Avatar.DamageStatsType")
}

fn read_finish_reasons(session: &Session<'_>, key: &'static str) -> Result<Json, ConstantsError> {
    let reason = session.value_at(key, "BattleDefinitions", &["FinishReason"])?;
    let values_method = session
        .vm
        .getattr_str(&reason, "values")
        .map_err(|signal| session.failure(key, "FinishReason.values", signal))?;
    let names_method = session
        .vm
        .getattr_str(&reason, "names")
        .map_err(|signal| session.failure(key, "FinishReason.names", signal))?;
    let values = session.call(key, &values_method, "FinishReason.values()")?;
    let names = session.call(key, &names_method, "FinishReason.names()")?;

    let values = session.vm.collect(&values).map_err(|signal| session.failure(key, "FinishReason.values()", signal))?;
    let names = session.vm.collect(&names).map_err(|signal| session.failure(key, "FinishReason.names()", signal))?;
    let entries = values.into_iter().zip(names).collect();
    let dict = session.dict_of(key, entries, "FinishReason")?;

    session.json(key, &dict, "FinishReason")
}

fn read_death_reasons(session: &Session<'_>, key: &'static str) -> Result<Json, ConstantsError> {
    let registry = session.value_at(key, "Vehicle", &["DeathReason", "_DeathReason__byId"])?;
    let Value::Object(registry) = &registry else {
        return session.json(key, &registry, "Vehicle.DeathReason._DeathReason__byId");
    };

    let mut entries = Vec::new();
    for (id, reason) in session
        .vm
        .dict_items(registry)
        .map_err(|signal| session.failure(key, "Vehicle.DeathReason._DeathReason__byId", signal))?
    {
        let attributes = session
            .vm
            .getattr_str(&reason, "__dict__")
            .map_err(|signal| session.failure(key, "vars(DeathReason)", signal))?;
        entries.push((id, attributes));
    }

    let dict = session.dict_of(key, entries, "Vehicle.DeathReason")?;

    session.json(key, &dict, "Vehicle.DeathReason._DeathReason__byId")
}

fn read_shared_info(session: &Session<'_>, key: &'static str, global: &str) -> Result<Json, ConstantsError> {
    let gate = session.mods_api(key, "battleGate")?;
    let players = session
        .vm
        .getattr_str(&gate, "PlayersInfo")
        .map_err(|signal| session.failure(key, "battleGate.PlayersInfo", signal))?;
    let info = session
        .vm
        .getattr_str(&players, global)
        .map_err(|signal| session.failure(key, &format!("PlayersInfo.{global}"), signal))?;
    let map = session
        .vm
        .getattr_str(&info, "_numMemberMap")
        .map_err(|signal| session.failure(key, &format!("PlayersInfo.{global}._numMemberMap"), signal))?;

    session.json(key, &map, &format!("PlayersInfo.{global}._numMemberMap"))
}
