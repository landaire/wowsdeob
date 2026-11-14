//! Conversion of interpreter values to JSON with the rules of Python 2's
//! `json.dump`, keeping dict iteration order.

use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Write;
use std::rc::Rc;

use unfuck::interp::Value;
use unfuck::interp::Vm;
use unfuck::interp::numbers;
use unfuck::interp::numbers::Integral;
use unfuck::interp::value::Payload;

use crate::constants::error::ConstantsError;

/// JSON string content as UTF-16 code units. Python 2 `unicode` values may
/// hold unpaired surrogates, which `json.dump` writes as `\uXXXX` escapes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsonText(Vec<u16>);

impl JsonText {
    pub fn units(&self) -> &[u16] {
        &self.0
    }
}

impl From<&str> for JsonText {
    fn from(text: &str) -> Self {
        Self(text.encode_utf16().collect())
    }
}

impl std::fmt::Display for JsonText {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&String::from_utf16_lossy(&self.0))
    }
}

/// A JSON document whose objects keep their key order.
#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    /// Integer text, exact for Python longs.
    Integer(String),
    /// Float text as Python's `repr` renders it.
    Float(String),
    String(JsonText),
    Array(Vec<Json>),
    Object(Vec<(JsonText, Json)>),
}

impl Json {
    /// The value of `key` when this is an object that has it.
    pub fn get(&self, key: &str) -> Option<&Json> {
        let Self::Object(entries) = self else {
            return None;
        };

        let key = JsonText::from(key);

        entries.iter().find(|(name, _)| *name == key).map(|(_, value)| value)
    }

    /// Pretty-printed with two-space indentation.
    pub fn render(&self) -> String {
        let mut output = String::new();
        self.write(&mut output, 0);
        output.push('\n');

        output
    }

    fn write(&self, output: &mut String, depth: usize) {
        match self {
            Self::Null => output.push_str("null"),
            Self::Bool(flag) => output.push_str(if *flag { "true" } else { "false" }),
            Self::Integer(text) | Self::Float(text) => output.push_str(text),
            Self::String(text) => write_string(output, text),
            Self::Array(items) => {
                if items.is_empty() {
                    output.push_str("[]");
                    return;
                }
                output.push('[');
                for (index, item) in items.iter().enumerate() {
                    output.push_str(if index == 0 { "\n" } else { ",\n" });
                    indent(output, depth + 1);
                    item.write(output, depth + 1);
                }
                output.push('\n');
                indent(output, depth);
                output.push(']');
            }
            Self::Object(entries) => {
                if entries.is_empty() {
                    output.push_str("{}");
                    return;
                }
                output.push('{');
                for (index, (key, value)) in entries.iter().enumerate() {
                    output.push_str(if index == 0 { "\n" } else { ",\n" });
                    indent(output, depth + 1);
                    write_string(output, key);
                    output.push_str(": ");
                    value.write(output, depth + 1);
                }
                output.push('\n');
                indent(output, depth);
                output.push('}');
            }
        }
    }
}

fn indent(output: &mut String, depth: usize) {
    for _ in 0..depth {
        output.push_str("  ");
    }
}

/// `json.dump`'s default ASCII output: printable ASCII as is, the short
/// escapes, and every other code unit as `\uXXXX`.
fn write_string(output: &mut String, text: &JsonText) {
    output.push('"');

    for unit in text.units() {
        match *unit {
            0x22 => output.push_str("\\\""),
            0x5c => output.push_str("\\\\"),
            0x0a => output.push_str("\\n"),
            0x0d => output.push_str("\\r"),
            0x09 => output.push_str("\\t"),
            0x08 => output.push_str("\\b"),
            0x0c => output.push_str("\\f"),
            printable @ 0x20..=0x7e => output.push(char::from(printable as u8)),
            other => {
                let _ = write!(output, "\\u{other:04x}");
            }
        }
    }

    output.push('"');
}

/// Converts a value as `json.dump` would with an encoder that writes sets as
/// sorted lists.
pub struct Converter<'a> {
    pub vm: &'a Vm,
    pub key: &'static str,
    /// Containers being converted, by address, to reject cycles as
    /// `json.dump`'s circular reference check does.
    active: RefCell<HashSet<usize>>,
}

impl<'a> Converter<'a> {
    pub fn new(vm: &'a Vm, key: &'static str) -> Self {
        Self { vm, key, active: RefCell::new(HashSet::new()) }
    }
}

impl Converter<'_> {
    pub fn convert(&self, value: &Value, path: &str) -> Result<Json, ConstantsError> {
        let vm = self.vm;

        match value {
            Value::None => return Ok(Json::Null),
            Value::Bool(flag) => return Ok(Json::Bool(*flag)),
            Value::Unknown(unknown) => {
                return Err(ConstantsError::Unknown {
                    key: self.key,
                    path: path.to_owned(),
                    origin: unknown.origin.clone(),
                });
            }
            _ => {}
        }

        if let Some(integral) = vm.as_integral(value) {
            return Ok(Json::Integer(integral_text(&integral)));
        }
        if let Some(number) = vm.as_float(value) {
            return Ok(Json::Float(float_text(number)));
        }
        if let Some(text) = self.text(value, path)? {
            return Ok(Json::String(text));
        }
        if let Some(items) = vm.as_tuple(value) {
            return self.array(&items, path);
        }

        let Value::Object(object) = value else {
            return Err(self.unserializable(value, path));
        };

        let address = Rc::as_ptr(object) as usize;
        if !self.active.borrow_mut().insert(address) {
            return Err(ConstantsError::Circular { key: self.key, path: path.to_owned() });
        }
        let converted = self.container(value, object, path);
        self.active.borrow_mut().remove(&address);

        converted
    }

    fn container(
        &self,
        value: &Value,
        object: &unfuck::interp::value::ObjectRef,
        path: &str,
    ) -> Result<Json, ConstantsError> {
        let vm = self.vm;

        match &object.payload {
            Payload::List(items) => {
                let items = items.borrow().clone();
                self.array(&items, path)
            }
            Payload::Dict(_) => self.object(&vm.dict_items(object).map_err(|signal| self.signal(signal, path))?, path),
            Payload::DictProxy(dict) => {
                self.object(&vm.dict_items(dict).map_err(|signal| self.signal(signal, path))?, path)
            }
            Payload::Set(_) | Payload::FrozenSet(_) => {
                let Some(mut items) = vm.set_items(value) else {
                    return Err(self.unserializable(value, path));
                };
                vm.sort_values(&mut items, None, None, false).map_err(|signal| self.signal(signal, path))?;
                self.array(&items, path)
            }
            _ => Err(self.unserializable(value, path)),
        }
    }

    fn array(&self, items: &[Value], path: &str) -> Result<Json, ConstantsError> {
        let converted = items
            .iter()
            .enumerate()
            .map(|(index, item)| self.convert(item, &format!("{path}[{index}]")))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Json::Array(converted))
    }

    fn object(&self, entries: &[(Value, Value)], path: &str) -> Result<Json, ConstantsError> {
        let mut converted = Vec::with_capacity(entries.len());

        for (key, value) in entries {
            let name = self.key_text(key, path)?;
            let child = self.convert(value, &format!("{path}[\"{name}\"]"))?;
            converted.push((name, child));
        }

        Ok(Json::Object(converted))
    }

    /// Dict keys as `json.dump` writes them: strings as is, numbers and
    /// constants in their JSON spelling.
    fn key_text(&self, key: &Value, path: &str) -> Result<JsonText, ConstantsError> {
        match key {
            Value::None => return Ok(JsonText::from("null")),
            Value::Bool(flag) => return Ok(JsonText::from(if *flag { "true" } else { "false" })),
            Value::Unknown(unknown) => {
                return Err(ConstantsError::Unknown {
                    key: self.key,
                    path: path.to_owned(),
                    origin: unknown.origin.clone(),
                });
            }
            _ => {}
        }

        if let Some(text) = self.text(key, path)? {
            return Ok(text);
        }
        if let Some(integral) = self.vm.as_integral(key) {
            return Ok(JsonText::from(integral_text(&integral).as_str()));
        }
        if let Some(number) = self.vm.as_float(key) {
            return Ok(JsonText::from(float_text(number).as_str()));
        }

        Err(self.unserializable(key, path))
    }

    /// Text of `str` (decoded as UTF-8, `json`'s default) or `unicode`.
    fn text(&self, value: &Value, path: &str) -> Result<Option<JsonText>, ConstantsError> {
        if let Some(bytes) = self.vm.as_str_bytes(value) {
            return match std::str::from_utf8(bytes.as_bytes()) {
                Ok(text) => Ok(Some(JsonText::from(text))),
                Err(_) => Err(ConstantsError::Unserializable {
                    key: self.key,
                    path: path.to_owned(),
                    type_name: "str (not UTF-8)".to_owned(),
                }),
            };
        }

        Ok(self.vm.as_text(value).map(|text| JsonText(text.units().to_vec())))
    }

    fn unserializable(&self, value: &Value, path: &str) -> ConstantsError {
        ConstantsError::Unserializable { key: self.key, path: path.to_owned(), type_name: self.vm.type_name(value) }
    }

    fn signal(&self, signal: unfuck::interp::Signal, path: &str) -> ConstantsError {
        ConstantsError::Evaluation {
            key: self.key,
            expression: path.to_owned(),
            detail: crate::constants::extract::describe_signal(self.vm, &signal),
        }
    }
}

fn integral_text(integral: &Integral) -> String {
    match integral {
        Integral::Int(number) => number.to_string(),
        Integral::Long(number) => number.to_string(),
    }
}

/// `float.__repr__`, which `json` uses, except for the non-finite values it
/// spells `NaN`, `Infinity`, and `-Infinity`.
fn float_text(number: f64) -> String {
    if number.is_nan() {
        return "NaN".to_owned();
    }
    if number.is_infinite() {
        return if number > 0.0 { "Infinity" } else { "-Infinity" }.to_owned();
    }

    numbers::float_repr(number)
}

#[cfg(test)]
mod tests {
    use super::Json;
    use super::JsonText;

    #[test]
    fn strings_render_as_ascii_with_unit_escapes() {
        let text = JsonText(vec![0x41, 0x22, 0x0a, 0xe9, 0xd83d, 0xde00, 0xd800]);

        assert_eq!(Json::String(text).render(), "\"A\\\"\\n\\u00e9\\ud83d\\ude00\\ud800\"\n");
    }
}
