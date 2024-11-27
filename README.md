# Special Numbers

Formalization of Chapter 6, Special Numbers, of Concrete Mathematics.

## Usage

The package includes a Nix flake that provides a development environment with all
the necessary tools, including a setup of Lean itself.

Run the development environment with `nix develop`.

Once in the shell, run `task -a` to list the tasks available for building the package
and its documentation.

For the simplest use case, run `task build` for building the package. And run
`task serve-docs` to build and render the documentation.

### Notes

The tasks ensure that the Mathlib cache is available, so there is no need to run the
usual `lake exe cache get`.

## Authors

* Walter Moreira
* Joe Stubbs

## License

MIT