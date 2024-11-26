# Special Numbers

Formalization of Chapter 6, Special Numbers, of Concrete Mathematics.

## Building the package

Ensure Mathlib is downloaded from cache with `lake exe cache get`.

Build the package with `lake build`.

## Building the documentation

Build the documentation with:
```
cd docbuild
lake build SpecialNumbers:docs
```

Access the documentation by running:
```
python3 -m http.server -d .lake/build/doc
```