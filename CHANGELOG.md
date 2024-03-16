# Changelog for `iso`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

## 0.1.1.0 - 2024/3/12

### Implemented Parser Using FlatParse Library
More testing needed
TODO:
1. Support multiple bound variable
2. Impl keywords list using macro expansion

### Concrete Syntax:
- Show Int type as `Int` instead of `Nat`
- Show Changed Mu types using capital M in consistent with other types, moved the dot position to after variable name


### AST Changes Suggestion:
1. `zip` the two lists in `IsoValue`, so the two are always the same length
2. The paper suggests `PtMultiVar` syntax using nested tuples, which is different from our AST, and perhaps easier to type check?
3. `ExpLet` is also different from the paper, which always has an iso on the rhs. 
4. Change the module name `Data`?
