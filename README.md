# Taranis

> **Taranis** (/təˈrænɪs/): Celtic god of thunder and the wheel.

Taranis is a scheduler for *cykelphester* (progressive dinners / safari suppers), written using the constraint programming language MiniZinc. Currently only a proof of concept, but more features are planned.

## Dependencies

- [The MiniZinc compiler](https://www.minizinc.org/downloads/)

## Running

  ```sh
  git clone git@github.com:Dsek-LTH/taranis.git
  cd taranis
  minizinc cykelphest.mzn
  ```

## Planned features

- Web GUI (either on [dsek.se](https://dsek.se) or on its own)
- Travel distance minimization based on given distances
  - Coordinate lookup from addresses?
