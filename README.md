USER MANUAL FOR DEDUKTI (DEVELOPMENT VERSION)
=============================================

### INSTALLATION

To compile (and optionally install) `Dedukti` you will need:
 - `OCaml >= 4.02`,
 - `Menhir`,
 - `OCamlBuild` (build only),
 - `OCamlFind` (build only).

#### INSTALLATION WITH OPAM

```bash
opam install dedukti
```

#### INSTALLATION FROM SOURCE

```bash
git clone https://github.com/Deducteam/Dedukti.git
cd Dedukti
make
sudo make install
```

### QUICK START (ASSUMING INSTALLATION)

The command
```bash
dkcheck examples/append.dk
```
should output the following.
```
SUCCESS File 'examples/append.dk' was successfully checked.
```

### COMMAND LINE PROGRAMS

The installation provides the following commands:
 - `dkcheck` is the type-checker for `Dedukti`,
 - `dktop` is an interactive wrapper around the type-checker,
 - `dkdep` is a dependency generator for `Dedukti` files,
 - `dkindent` is a program to indent `Dedukti` files.

### OPTIONS

`dkcheck` provides the following options:
 - `-e` Generates an object file `.dko`;
 - `-I DIR` Adds the directory `DIR` to the load path;
 - `-d FLAGS` enables debugging for all given flags:
   * `q` (*q*uiet) disables all warnings,
   * `n` (*n*otice) notifies about which symbol or rule is currently treated,
   * `o` (m*o*dule) notifies about loading of an external module (associated to the command `#REQUIRE`),
   * `c` (*c*onfluence) notifies about information provided to the confluence checker (when option `-cc` used),
   * `u` (r*u*le) provides information about type checking of rules,
   * `t` (*t*yping) provides information about type-checking of terms,
   * `r` (*r*educe) provides information about reduction performed in terms,
   * `m` (*m*atching) provides information about pattern matching;
 - `-v` Verbose mode (equivalent to `-d montru`;
 - `-q` Quiet mode (equivalent to `-d q`;
 - `--no-color` Disables colors in the output;
 - `--stdin MOD` Parses standard input using module name `MOD`;
 - `--coc` [Experimental] Allows to declare a symbol whose type contains `Type` in the left-hand side of a product (useful for the Calculus of Construction);
 - `--type-lhs` Forbids rules with untypable left-hand side;
 - `--snf` Normalizes the types in error messages;
 - `--confluence CMD` Sets the external confluence checker command to `CMD`;
 - `--beautify` Pretty printer. Prints on the standard output;
 - `--version` Prints the version number;
 - `--help` Prints the list of available options.

### A SMALL EXAMPLE

Then we can declare constants, giving their name and their type.
`Dedukti` distinguishes two kinds of declarations:

* declaration of a *static* symbol `f` of type `A` is written `f : A`,
* declaration of a *definable* symbol `f` of type `A` is written `def f : A`.

Definable symbols can be defined using rewrite rules, static symbols can not be defined.

    Nat: Type.
    zero: Nat.
    succ: Nat -> Nat.
    def plus: Nat -> Nat -> Nat.

Let's add rewrite rules to compute additions.

    [ n ] plus zero n --> n
    [ n ] plus n zero --> n
    [ n, m ] plus (succ n) m --> succ (plus n m)
    [ n, m ] plus n (succ m) --> succ (plus n m).

When adding rewrite rules, `Dedukti` checks that they preserve typing.
For this, it checks that the left-hand and right-hand sides of the rules have the same type in some context giving types to the free variables
(in fact, the criterion used is more general, see below), that the free variables occurring in the right-hand side also occur in the left-hand side
and that the left-hand side is a *higher-order pattern* (see below).

**Remark:** there is no constraint on the number of rewrite rules associated with a definable symbol.
However it is necessary that the rewrite system generated by the rewrite rules together with beta-reduction
be confluent and terminating on well-typed terms. Confluence can be checked using the option `-cc` (see below),
termination is not checked (yet?).

**Remark:** Because static symbols cannot appear at head of rewrite rules, they are injective with respect to conversion and this information can be exploited by
`Dedukti` for type-checking rewrite rules (see below).

### ADVANCED FEATURES

#### SPLITTING A DEVELOPMENT BETWEEN SEVERAL FILES

A development in `Dedukti` is usually composed of several files corresponding to different modules.
Using `dkcheck` with the option `-e` will produce a file `my_module.dko` that exports the constants
and rewrite rules declared in the module `my_module`.
Then you can use these symbols in other files/modules using the prefix notation `my_module.identifier`.

#### COMMENTS

In `Dedukti` comments are delimited by `(;` and `;)`.

    (; This is a comment ;)

#### COMMANDS

Supported commands are:

    #EVAL t.             (; evaluate t to its strong normal form and display it. ;)
    #EVAL[N].            (; same as above, but evaluate in at most N steps. ;)
    #EVAL[STRAT].        (; evaluate t with the strategy STRAT. :)
    #EVAL[N,STRAT].      (; same as above, but evaluate in at most N steps. :)
    #CHECK t1 == t2.     (; display "YES" if t1 and t2 are convertible, "NO" otherwise. ;)
    #CHECK t1 : t2.      (; display "YES" if t1 has type t2, "NO" otherwise. ;)
    #CHECKNOT t1 == t2.  (; display "YES" if t1 and t2 are not convertible, "NO" otherwise. ;)
    #CHECKNOT t1 : t2.   (; display "YES" if t1 does not have type t2, "NO" otherwise. ;)
    #ASSERT t1 : t2.     (; fail if t1 does not have type t2. ;)
    #ASSERT t1 == t2.    (; fail if t1 is not convertible with t2. ;)
    #ASSERTNOT t1 : t2.  (; fail if t1 does have type t2. ;)
    #ASSERTNOT t1 == t2. (; fail if t1 is convertible with t2. ;)
    #INFER t1.           (; infer the type of t1 and display it. ;)
    #PRINT s.            (; print the string s. ;)

The supported evaluation strategies are:
 - `SNF` (strong normal form: a term `t` is in `SNF` if no reduction can occur in `t`),
 - `WHNF` (weak head normal form: a term `t` is said in `WHNF` if there is a finite sequence `t=t0`, `t2`, ..., `tn` such that `tn` is in normal form and for all `i`, `ti` reduces to `t(i+1)` and this reduction does not occur at the head).

Note that the `#INFER` command accepts the same form of configuration as
the `#EVAL` command. When given, it is used to evaluate the obtained type.

#### DEFINITIONS

`Dedukti` supports definitions:

    def three : Nat := succ ( succ ( succ ( zero ) ) ).

or, omitting the type,

    def three := succ ( succ ( succ ( zero ) ) ).

A definition is syntactic sugar for a declaration followed by a rewrite rule.
The definition above is equivalent to:

    def three : Nat.
    [ ] three --> succ ( succ ( succ ( zero ) ) ).

Using the keyword `thm` instead of `def` makes a definition *opaque*, meaning that the defined symbol do not reduce
to the body of the definition. This means that the rewrite rule is not added to the system.

    thm three := succ ( succ ( succ ( zero ) ) ).

This can be useful when the body of a definition does not matter (only its existence matters), to avoid adding
a useless rewrite rule.

#### JOKERS

When a variable is not used on the right-hand side of a rewrite rule, it can be
replaced by an underscore on the left-hand side.

    def mult : Nat -> Nat -> Nat.
    [ n ] mult zero n --> zero
    [ n, m ] mult (succ n) m --> plus m (mult n m).

The first rule can also be written:

    [ ] mult zero _ --> zero.

#### TYPING OF REWRITE RULES

A typical example of the use of dependent types is the type of Vector defined as lists parametrized by their size:

    Elt: Type.
    Vector: Nat -> Type.
    nil: Vector zero.
    cons: n:Nat -> Elt -> Vector n -> Vector (succ n).

and a typical operation on vectors is concatenation:

    def append: n:Nat -> Vector n -> m:Nat -> Vector m -> Vector (plus n m).
    [ n, v ] append zero nil n v --> v
    [ n, v1, m, e, v2 ] append (succ n) (cons n e v1) m v2 --> cons (plus n m) e (append n v1 m v2).

These rules verify the typing constraint given above: both left-hand and right-hand sides have the same type.

Also, the second rule is non-left-linear; this is usually an issue because non-left-linear rewrite rules usually generate
a non-confluent rewrite system when combined with beta-reduction.

However, because we only intend to rewrite *well-typed* terms, the rule above is computationally equivalent to the following left-linear rule:

    [ n, v1, m, e, v2, x ] append x (cons n e v1) m v2 --> cons (plus n m) e (append n v1 m v2).

`Dedukti` will also accept this rule, even if the left-hand side is not well-typed, because it is able to detect that, because of typing
constraints, `x` can only be instantiated by a term of the form `succ n`
(this comes from the fact that `Vector` is a static symbol and is
hence injective with respect to conversion: from the type-checking constraint `Vector x = Vector (succ n)`, `Dedukti` deduces `x = succ n`).


For the same reason, it is not necessary to check that the first argument of `append` is `zero` for the first rule:

    [ n, v, x ] append x nil n v --> v.

Using underscores, we can write:

    [ v ] append _ nil _ v --> v
    [ n, v1, m, e, v2 ] append _ (cons n e v1) m v2 --> cons (plus n m) e (append n v1 m v2).

#### TYPE ANNOTATIONS

Variables in the context of a rule may be annotated with their expected type.
It is checked that the inferred type for annotated rule variables are convertible
with the provided annotation.

    [ n : Nat
    , v1 : Vector n
    , m : Nat
    , e : Elt
    , v2  : Vector m ]
      append _ (cons n e v1) m v2 --> cons (plus n m) e (append n v1 m v2).

#### BRACKET PATTERNS

A different solution to the same problem is to mark with brackets the parts of the left-hand
side of the rewrite rules that are constrained by typing.

    [ n, v1, m, e, v2 ] append (succ n) (cons {n} e v1) m v2 --> cons (plus n m) e (append n v1 m v2).

The information between brackets will be used when typing the rule but they will not be match against when
using the rule (as if they were replaced by unapplied fresh variables).

**Remarks:**
- in order to make this feature type-safe, `Dedukti` checks at runtime that the bracket constraint is verified
whenever the rule may be used and fails otherwise.
- This feature is not conditional rewriting. When a constraints is not satisfied, Dedukti doesn't just ignore
the rule and proceed, it actually raises an error.
- because they are replaced with *unapplied* fresh variables, bracket expressions may not contain variables
locally bounded previously in the pattern.
- since they are not used during matching, bracket expressions may not "introduce" variables. All rule variables
occuring in bracket expression need to also occur in an other part of the pattern, outside a bracket.
- bracket expressions and their type may contain variables occuring "before" (to the left of) the pattern.
- the type of a bracket expression may not contain variables occuring for the first time "after" (to the right of)
the bracket.
- the bracket expression may contain variable occuring for the first time "after" (to the right of) the bracket on
the condition that the inferred types for these variables do not depend on the bracket's fresh variable (no circularity).



#### NON-LEFT-LINEAR REWRITE RULES

By default, `Dedukti` rejects non-left-linear rewrite rules because they usually generated non confluent rewrite systems
when combined with beta-reduction. This behaviour can be changed by invoking `dkcheck` with the option `-nl`.

    eq: Nat -> Nat -> Bool.
    [ n ] eq n n --> true.

#### HIGHER-ORDER REWRITE RULES

In the previous examples, left-hand sides of rewrite rules were first-order terms.
In fact, `Dedukti` supports a larger class of left-hand sides: *higher-order patterns*.

A *higher-order pattern* is a beta-normal term whose free variables are applied to (possibly empty) vectors of distinct bound variables.

A classical example of the use of higher-order rules is the encoding the simply types lambda-calculus with beta-reduction:

    type: Type.
    arrow: type -> type -> type.

    term: type -> Type.

    def app: a:type -> b:type -> term (arrow a b) -> term a -> term b.
    lambda: a:type -> b:type -> (term a -> term b) -> term (arrow a b).

    [ f, arg ] app _ _ (lambda _ _ (x => f x)) arg --> f arg.

**Remark:** type annotations on abstraction *must* be omitted.

**Remark:** free variables must be applied to the same number of arguments on the left-hand side and on the right-hand side
of the rule.

**Remark:** with such rewrite rules, matching is done modulo beta in order to preserve confluence.
This means that, in the context `(o: type)(c:term o)`, the term `App o o (Lam o o (x => x)) c` reduces to `c`.

#### CONFLUENCE CHECKING

`Dedukti` can check the confluence of the rewrite system generated by the rewrite rules and beta-reduction,
using an external confluence checker. For this you need to install a confluence checker for higher-order rewrite systems
supporting the TPDB format, for instance [CSI^HO](http://cl-informatik.uibk.ac.at/software/csi/ho/) or ACPH.

To enable confluence checking you need to call `dkcheck` with the option `-cc` followed by the path to the confluence checker:

    $ dkcheck -cc /path/to/csiho.sh examples/append.dk
    > File examples/append.dk was successfully checked.

### LICENSE

`Dedukti` is distributed under the CeCILL-B License.
