//! What the interpreter needs to know about the World of Warships client
//! engine to run its scripts the way the client does.

use unfuck::interp::PyResult;
use unfuck::interp::Value;
use unfuck::interp::Vm;
use unfuck::interp::value::ObjectRef;

/// Modules the engine imports at startup, in order: `bw_site` (which sets
/// the UTF-8 default encoding and imports `BWAutoImport`), then the
/// personality script.
pub const STARTUP_MODULES: &[&str] = &["bw_site", "BWPersonality"];

/// Installs the engine facts into an interpreter.
pub fn register(vm: &Vm) {
    vm.register_import_hook("BigWorld", describe_bigworld);
}

/// `BigWorld` is native. Scripts branch on which engine component runs
/// them; everything else in it stays unknown.
fn describe_bigworld(vm: &Vm, module: &ObjectRef) -> PyResult<()> {
    vm.setattr_str(&Value::Object(std::rc::Rc::clone(module)), "component", Value::str("client"))
}
