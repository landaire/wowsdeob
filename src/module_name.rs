use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModuleKind {
    Module,
    /// A package, loaded from its `__init__.pyc`.
    Package,
}

/// The dotted import name of a module in `scripts.zip`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModuleName {
    dotted: String,
    kind: ModuleKind,
}

impl ModuleName {
    /// Maps a `scripts.zip` entry path to its import name: `scripts/Foo/Bar.pyc` is
    /// module `Foo.Bar` and `scripts/Foo/__init__.pyc` is package `Foo`. Returns
    /// `None` for entries that are not importable `.pyc` files.
    pub fn from_zip_path(path: &str) -> Option<Self> {
        let relative = path.strip_prefix("scripts/")?.strip_suffix(".pyc")?;

        let (dotted_path, kind) = match relative.strip_suffix("/__init__") {
            Some(package) => (package, ModuleKind::Package),
            None => (relative, ModuleKind::Module),
        };

        let mut dotted = String::with_capacity(dotted_path.len());
        for component in dotted_path.split('/') {
            if component.is_empty() || component.contains('.') || component == "__init__" {
                return None;
            }
            if !dotted.is_empty() {
                dotted.push('.');
            }
            dotted.push_str(component);
        }

        Some(Self { dotted, kind })
    }

    pub fn as_str(&self) -> &str {
        &self.dotted
    }

    pub fn kind(&self) -> ModuleKind {
        self.kind
    }

    pub fn is_package(&self) -> bool {
        self.kind == ModuleKind::Package
    }
}

impl fmt::Display for ModuleName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.dotted)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_zip_paths() {
        let cases = [
            "scripts/Account.pyc",
            "scripts/Foo/Bar.pyc",
            "scripts/Foo/__init__.pyc",
            "scripts/Foo/Bar/__init__.pyc",
            "scripts/__init__.pyc",
            "scripts/Foo/",
            "scripts/Foo.py",
            "other/Foo.pyc",
            "scripts/Foo//Bar.pyc",
            "scripts/Foo.Bar/Baz.pyc",
            "scripts/Foo/x__init__.pyc",
        ];

        let mapped: Vec<String> = cases
            .iter()
            .map(|path| match ModuleName::from_zip_path(path) {
                Some(name) => format!("{path} -> {name} ({:?})", name.kind()),
                None => format!("{path} -> none"),
            })
            .collect();

        assert_eq!(
            mapped,
            [
                "scripts/Account.pyc -> Account (Module)",
                "scripts/Foo/Bar.pyc -> Foo.Bar (Module)",
                "scripts/Foo/__init__.pyc -> Foo (Package)",
                "scripts/Foo/Bar/__init__.pyc -> Foo.Bar (Package)",
                "scripts/__init__.pyc -> none",
                "scripts/Foo/ -> none",
                "scripts/Foo.py -> none",
                "other/Foo.pyc -> none",
                "scripts/Foo//Bar.pyc -> none",
                "scripts/Foo.Bar/Baz.pyc -> none",
                "scripts/Foo/x__init__.pyc -> Foo.x__init__ (Module)",
            ]
        );
    }
}
