//! Extraction from a real game install. Run with
//! `WOWS_GAME_DIR=<install> cargo test --release --test constants_install -- --ignored`.

use std::collections::BTreeSet;
use std::path::Path;

use wowsdeob::constants::ClientBuild;
use wowsdeob::constants::Constants;
use wowsdeob::constants::HostAccess;
use wowsdeob::constants::Json;
use wowsdeob::constants::extract;

/// The keys of `constants.json` that come from the client scripts.
/// `BATTLE_TYPES` is sent by the server at login.
const EXPECTED_KEYS: &[&str] = &[
    "BATTLE_STAGES",
    "BOT_NUM_MEMBER_MAP",
    "CLIENT_BUILDING_INTERACTION_DETAILS",
    "CLIENT_PUBLIC_RESULTS",
    "CLIENT_PUBLIC_RESULTS_INDICES",
    "CLIENT_VEH_INTERACTION_DETAILS",
    "COMMON_ECONOMICS",
    "COMMON_ECONOMICS_INDICES",
    "COMMON_RESULTS",
    "CONSUMABLE_IDS",
    "DAMAGE_STATS",
    "DEATH_REASONS",
    "FINISH_REASONS",
    "GAME_MODES",
    "INIT_ECONOMICS",
    "INIT_ECONOMICS_INDICES",
    "OBSERVER_NUM_MEMBER_MAP",
    "PLAYER_FULL_RESULTS",
    "PLAYER_NUM_MEMBER_MAP",
    "PLAYER_PRIVATE_RESULTS",
    "PLAYER_PRIVATE_RESULTS_INDICES",
    "RIBBONS",
    "SHARED_DATA_CONSTANTS",
    "SHIP_TYPES",
    "SKILLS_BY_SHIP_TYPE",
    "SUBTOTAL_ECONOMICS",
    "SUBTOTAL_ECONOMICS_INDICES",
    "UNIT_TYPES",
    "VERSION",
];

/// The constants of the newest build under `WOWS_GAME_DIR`.
fn installed_constants() -> Constants {
    let game_dir = std::env::var_os("WOWS_GAME_DIR").expect("WOWS_GAME_DIR names a game install");
    let build = ClientBuild::find(Path::new(&game_dir), None).expect("the install has a build with client scripts");

    let extraction = extract(&build, HostAccess::deny_all()).expect("the interpreter runs");
    match extraction.constants {
        Ok(constants) => constants,
        Err(error) => panic!("extraction failed: {error}"),
    }
}

#[test]
#[ignore = "needs a World of Warships install named by WOWS_GAME_DIR"]
fn installed_build_yields_every_script_key() {
    let constants = installed_constants();
    let Json::Object(entries) = constants.json() else {
        panic!("constants are not a JSON object");
    };

    let produced: BTreeSet<String> = entries.iter().map(|(key, _)| key.to_string()).collect();
    let expected: BTreeSet<String> = EXPECTED_KEYS.iter().map(|key| (*key).to_owned()).collect();
    assert_eq!(produced, expected);
}

#[test]
#[ignore = "needs a World of Warships install named by WOWS_GAME_DIR"]
fn repeated_extractions_render_identical_output() {
    assert_eq!(installed_constants().render(), installed_constants().render());
}
