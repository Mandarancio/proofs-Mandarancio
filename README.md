# Modeling & Verification Homework #2

This repository is the starter for homework #2 of the course
["Modeling & Verification"](https://moodle.unige.ch/course/view.php?id=183)
at [University of Geneva](http://www.unige.ch).

## Environment

Please install the [environment](https://github.com/cui-unige/modeling-verification).
Install also an additional library but running in a terminal the command:

```sh
  luarocks install rockspec/fun-scm-1.rockspec
  luarocks install rockspec/hashids-scm-1.rockspec
```

## Subject

You have to complete programs to check proofs on ADTs:

* write axioms for all operations in `src/adt/boolean.lua`;
* write axioms for all operations in `src/adt/natural.lua`;
* complete theorem generators in `src/adt/theorem.lua`;
* write the proof of `x+y = y+x` in `src/adt/theorem_spec.lua`.

You must only implement parts shown by `TODO` comments in the source code.
Do **not** touch other algorithms.
You are allowed to add extra functions if needed.

At the beginning, you already have:

* a representation for algebraic abstract data types (with tests);
* a representation for conjectures and theorems;
* parts of the Boolean and Natural data types;
* some theorem generators;
* some example proofs.

## Comments on Code

Modules/classes are in Uppercase, instances are in lowercase.
Look at tests! They are provided not only to check your code,
but also to show you examples of use of classes and methods.

### Iterators and Functions

We use [luafun](https://github.com/rtsisyk/luafun) to manipulate collections
and iterators.

* `Fun.all (predicate, iterator)` checks that all elements in `iterator`
  match `predicate`.
* `Fun.each (function, iterator)` applies `function` to all elements in
  `iterator`.
* `Fun.map (function, iterator)` applies `function` to all elements in
  `iterator` and returns an iterator over the results.
  If `function` returns one result, the iterator contains only values.
  If `function` returns two results, the iterator contains key-value pairs.
* `Fun.totable (iterator)` returns a Lua table built from elements in an
  `iterator` that contains only values.
  Elements in the table are indexed by numbers, starting at 1.
* `Fun.tomap (iterator)` returns a Lua table built from elements in an
  `iterator` that contains keys and values.
  Elements in the table are indexed by keys.
* Other functions to discover in the documentation!
* Methods can be chained, for instance: `Fun.frommap (t):map (...):tomap ()`.

### Algebraic Abstract Data Types

The `Adt` module contains the following "classes":

* `Sort` to represent sorts;
* `Variable` to represent variables;
* `Operation` to represent operations (and generators);
* `Term` to represent terms;
* `Axiom` to represent axioms.

### Sort

* `Sort "sort"` returns a new sort that will be printed "sort".
* `sort [Adt.name]` returns the name of `sort`.
* `sort [Adt.axioms]` returns a table that stores the axioms for `sort`.
* `getmetatable (sort) == Adt.Sort` tests if `sort` is a sort.
* `tostring (sort)` returns a string representation of `sort`.
* `sort_1 == sort_2` tests if the two sorts are the same one.

### Variable

* `sort._variable` returns the variable `variable` of sort `sort`.
* `getmetatable (variable) == Adt.Variable` tests if `variable` is a variable.
* `tostring (variable)` returns a string representation of `variable`.
* `variable_1 == variable_2` tests if the two variables are the same one.
* `variable [Adt.Sort]` returns the sort of `variable`.
* `variable / mapping` returns a new term or variable that corresponds
  to `variable` where it has been replaced by what is given in `mapping`.
  `mapping` is a table that maps variables to terms or variables.
  It can be obtained by `Adt.Term.equivalence`.

### Operation

* `sort.operation = { ... }` creates a new operation with operator `operation`
  in `sort`. The result of `operation` is of type `sort` and its operands are
  listed in the table, that represents the parameters of the operation and
  their sorts.
  This table can be of the form `{ sort_1, sort_2, ... }`, of the form
  `{ key_1 = sort_1, key_2 = sort_2, ... }` or a mix of these two forms.
* `getmetatable (operation) == Adt.Operation` tests if `operation` is an
  operation.
* `tostring (operation)` returns a string representation of `operation`.
* `operation_1 == operation_2` tests if the two operations are the same one.
* `operation [Adt.Sort]` returns the sort of `operation`.
* `operation { ... }` returns a term built using `operation`.
  This term is of the sort of `operation` and has the parameters passed in
  the table operand as arguments.
  This table can be of the form `{ term_1, term_2, ... }`, of the form
  `{ key_1 = term_1, key_2 = term_2, ... }` or a mix of these two forms.
  The terms must be of the sort described in the table passed at the creation
  of `operation`.

An iteration over the operands of an operation is usually written as below.
The `filter` is used to not take into account the `operation [Adt.Sort]` field.
```lua
result = Fun.frommap (operation)
       : filter (function (k) return type (k) ~= "table" end)
       : map (function (k, v) ... end)
  -- or all  (function (k, v) ... end)
  -- or each (function (k, v) ... end)
```

### Term

* Terms also have the following methods:
* `getmetatable (term) == Adt.Term` tests if `term` is a term.
* `tostring (term)` returns a string representation of `term`.
* `term_1 == term_2` tests if the two terms are equal.
* `term [Adt.Sort]` returns the sort of `term`.
* `term [Adt.Operation]` returns the operation of `term`.
* `ok, mapping = Adt.Term.equivalence (term_1, term_2)` tests if the two
  terms are equivalent, with a renaming of their variables.
  It returns two values, a boolean `ok` that is true if the terms are
  equivalent, and a `mapping` from variables to terms or variables, that
  can be used to rename variables in `term_1` and `term_2`.
* `term / mapping` returns a new term that corresponds to `term` where
  variables have been replaced by what is given in `mapping`.
  `mapping` is a table that maps variables to terms or variables.
  It can be obtained by `Adt.Term.equivalence`.

An iteration over the operands of a term is usually written similarly as below.
The `filter` is used to not take into account the `term [Adt.Sort]`
and `term [Adt.Operation]` fields.
```lua
result = Fun.frommap (term)
       : filter (function (k) return type (k) ~= "table" end)
       : map (function (k, v) ... end)
  -- or all  (function (k, v) ... end)
  -- or each (function (k, v) ... end)
```

The transformation of a term is usually written as below.
It obtains the term operation with `term [Operation]`,
and then calls it with the new term contents.
```lua
result = term [Operation] (Fun.frommap (term)
       : filter  (function (k, _) return type (k) ~= "table" end)
       : map     (function (k, v) ... end)
       : tomap ())
```

### Axiom

* `Adt.axiom { lhs, rhs, when = when }` returns an axiom of the form
  `when => lhs = rhs`.
   The `when` parameter is optional, but must be of `Boolean` sort if given.
   It differs from the slides, when a condition is a conjunction of
   term equalities.
* `sort [Adt.Axioms].myaxiom = Adt.axiom { ... }` allows to store the axiom
  with key `myaxiom`.
* `getmetatable (axiom) == Adt.Axiom` tests if `axiom` is an axiom.
* `tostring (axiom)` returns a string representation of `axiom`.
* `axiom_1 == axiom_2` tests if the two axioms are equal.

### Theorems

The `adt.theorem` module returns the `Theorem` class:

* `Theorem.Conjecture { lhs, rhs, when = when }` returns a conjecture of the
  form `when => lhs = rhs`.
  The `when` parameter is optional, but must be of `Boolean` sort if given.
* `Theorem { lhs, rhs, when = when, variables = variables }` returns a theorem
  of the form `when => lhs = rhs`.
  The `when` parameter is optional, but must be of `Boolean` sort if given.
  It differs from the slides, when a condition is a conjunction of
  term equalities.
  The `variables` parameter is a mapping from the variables used in axioms
  to the variables used in the theorem.
  It stores the mapping when a theorem is built above another one to allow
  easier manipulation.
* `getmetatable (theorem) == Theorem` tests if `theorem` is a theorem.
* `tostring (theorem)` returns a string representation of `theorem`.
* `theorem_1 == theorem_2` tests if the two theorems are equal.

### Theorem generators

* `Theorem.conjecture (conjecture)` creates a new theorem from `conjecture`.
  It must be used only internally by `Theorem.inductive`.
* `Theorem.axiom (axiom)` creates a new theorem from `axiom`.
* `Theorem.reflexivity (term)` creates a new theorem `term = term`.
* `Theorem.symmetry (theorem)` creates a new theorem
  `theorem.when => theorem [2] = theorem [1]`.
* `Theorem.transitivity (lhs, rhs)` creates a new theorem
  `lhs [1] = rhs [2]`.
  It must take into account the conditions of the theorems,
  contrary to the slides.
  If transitivity cannot apply, it returns `nil`.
* `Theorem.substitutivity (operation, operands)` applies substitutivity.
  It creates a new theorem by applying `operation` to the `operands`.
  `operands` is a table that corresponds to the operand of the operation,
  except that it contains theorems instead of terms.
  It must take into account the conditions of the theorems,
  contrary to the slides.
  If substitutivity cannot apply, it returns `nil`.
* `Theorem.substitution (theorem, variable, replacement)` applies substitution
  to `theorem`. `variable` is the variable to replace, and `replacement` is
  a term or variable to use as replacement.
  It must take into account the conditions of the theorem,
  contrary to the slides.
  If substitution cannot apply, it returns `nil`.
* `Theorem.cut (theorem, replacement)` applies `cut` to `theorem`.
  `replacement` is the `cond => u = u'` in the slides.
  If cut cannot apply, it returns `nil`.
  It works differently than in the course, because of our representation
  for conditions. Instead of looking for a term equality, `cut` has to
  search a `Boolean.Equals { ... }` term.
* `Theorem.inductive (conjecture, variable, t)` proves inductively
  `conjecture`.
  Table `t` is a mapping from the generators (type `Operation`) of the sort
  of `variable` to functions, that take as only parameter the conjecture
  seen as a theorem, and return the theorem proven when applying the
  generator on `variable`.
  `Theorem.inductive` proves the `conjecture` for all generators of
  the sort of `variable`, and thus proves the `conjecture` to be a theorem.

### Auxiliary functions

* The local function `simplify (term)` simplifies a Boolean expression
  used in conditions,
  for instance by removing it totally when it is `Boolean.True {}`.
* The local function `rename (term, variables)` renames all variables
  of `term` with fresh new variables.
  It is always used when building a new theorem or conjecture,
  so each theorem or conjecture uses a set of variables that totally differ
  from other theorems, conjectures and axioms.
  Take care to use `theorem.variables [v]` when referring to variable `v`
  of the axiom used to build `theorem`.
* `theorem.variables` or `conjecture.variables` are mappings from variables
  to variables, that stores as keys the variables of the original axiom used
  to create the theorem, and as values the equivalent variables in `theorem`.
* The local function `all_variables (x, variables)` puts in the `variable`
  table all variables used in the `x` parameter (that can be a theorem,
  a conjecture, an axiom, or a term).
  `variables` is a mapping where each variable is used both as a key and
  a value.
* The slides use term equality,
  for instance by using `t = t'` and `t' = t''` in transitivity.
  It is a shortcut, that the implementation must take into account:
  in our implementation, all theorems use different variables.
  In practice, when a term appears twice in a rule, you must use
  `Term.equivalence` between them instead of equality.
  You must also apply the obtained mapping to terms for correctness,
  using `term = term / mapping`.

### Proofs

A proof is a program starting with algebraic data types and axioms.
It applies `Theorem.*` functions to create new theorems until the theorem
to prove is reached.
You can store theorems in Lua variables and combine them as in a normal program.
Two proofs are given as examples in the tests of theorems.

## Tests

* All tests are put in `*_spec.lua` files.
* To run only some tests, add a tag to them (for example tag `#test`):

  ```lua
  describe ("#test ...", function () ...
  ```

  And then run from the root of the repository:

  ```
  $ busted --tags=test src/
  ```

## Rules

* We use [GitHub Classroom](https://classroom.github.com) for the homework.
* Ask your questions using GitHub issues in your repository.
* If for any reason you have trouble with the deadline,
  contact your teacher as soon as possible.
* Your source code (and tests) must pass all checks of `luacheck`
  without warnings or errors.
* Your tests must cover at least 80% of the source code (excluding test files).
* Your work will be tested in a dedicated environment, using `wercker`.
  You can always run all the tests on your code with the following command,
  from the root of your project (where the `wercker.yml` file is located):

  ```
  $ wercker build
  ```

## Evaluation

Evaluation follows the questions:

* do you have done anything at the deadline?
  (no: 0 points)
  * [x] Done anything
* do you have understood and implemented all the required notions?
  (yes: 4 points for all, no: 2 points for none)
  * [x]
* do you have understood and implemented corners cases of all the required
  notions?
  (yes: +2 point for all)
  * [x]
* do you have correctly written and tested your code?
  (no: -0.5 point for each)
  * [x] Coding standards
  * [x] Tests
  * [x] Code coverage

| Grade |
| ----- |
|   6   |
