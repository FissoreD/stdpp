This file lists "large-ish" changes to the std++ Coq library, but not every
API-breaking change is listed.

## std++ master

Coq 8.12 is newly supported by this release, and Coq 8.7 is no longer supported.

This release of std++ received contributions by Gregory Malecha, Michael
Sammler, Olivier Laurent, Paolo G. Giarrusso, Ralf Jung, Robbert Krebbers,
sarahzrf, and Tej Chajed.

- Rename `Z2Nat_inj_div` and `Z2Nat_inj_mod` to `Nat2Z_inj_div` and
  `Nat2Z_inj_mod` to follow the naming convention of `Nat2Z` and
  `Z2Nat`. Re-purpose the names `Z2Nat_inj_div` and `Z2Nat_inj_mod` for be the
  lemmas they should actually be.
- Add `rotate` and `rotate_take` functions for accessing a list with
  wrap-around. Also add `rotate_nat_add` and `rotate_nat_sub` for
  computing indicies into a rotated list.
- Add the `select` and `revert select` tactics for selecting and
  reverting a hypothesis based on a pattern.
- Extract `list_numbers.v` from `list.v` and `numbers.v` for
  functions, which operate on lists of numbers (`seq`, `seqZ`,
  `sum_list(_with)` and `max_list(_with)`). `list_numbers.v` is
  exported by the prelude. This is a breaking change if one only
  imports `list.v`, but not the prelude.
- Rename `drop_insert` into `drop_insert_gt` and add `drop_insert_le`.
- Add `Countable` instance for `Ascii.ascii`.
- Make lemma `list_find_Some` more apply friendly.
- Add `filter_app` lemma.
- Add tactic `multiset_solver` for solving goals involving multisets.
- Rename `fin_maps.singleton_proper` into `singletonM_proper` since it concerns
  `singletonM` and to avoid overlap with `sets.singleton_proper`.
- Add `wn R` for weakly normalizing elements w.r.t. a relation `R`.
- Add `encode_Z`/`decode_Z` functions to encode elements of a countable type
  as integers `Z`, in analogy with `encode_nat`/`decode_nat`.
- Fix list `Datatypes.length` and string `strings.length` shadowing (`length`
  should now always be `Datatypes.length`).
- Change the notation for pattern matching monadic bind into `'pat ← x; y`. It
  was `''pat ← x; y` (with double `'`) due to a shortcoming of Coq ≤8.7.

## std++ 1.3 (released 2020-03-18)

Coq 8.11 is supported by this release.

This release of std++ received contributions by Amin Timany, Armaël Guéneau,
Dan Frumin, David Swasey, Jacques-Henri Jourdan, Michael Sammler, Paolo G.
Giarrusso, Pierre-Marie Pédrot, Ralf Jung, Robbert Krebbers, Simon Friis Vindum,
Tej Chajed, and William Mansky

Noteworthy additions and changes:

- Rename `dom_map_filter` into `dom_map_filter_subseteq` and repurpose
  `dom_map_filter` for the version with the equality. This follows the naming
  convention for similar lemmas.
- Generalize `list_find_Some` and `list_find_None` to become bi-implications.
- Disambiguate Haskell-style notations for partially applied operators. For
  example, change `(!! i)` into `(.!! x)` so that `!!` can also be used as a
  prefix, as done in VST. A sed script to perform the renaming can be found at:
  https://gitlab.mpi-sws.org/iris/stdpp/merge_requests/93
- Add type class `TopSet` for sets with a `⊤` element. Provide instances for
  `boolset`, `propset`, and `coPset`.
- Add `set_solver` support for `dom`.
- Rename `vec_to_list_of_list` into `vec_to_list_to_vec`, and add new lemma
  `list_to_vec_to_list` for the converse.
- Rename `fin_of_nat` into `nat_to_fin`, `fin_to_of_nat` into
  `fin_to_nat_to_fin`, and `fin_of_to_nat` into `nat_to_fin_to_nat`, to follow
  the conventions.
- Add `Countable` instance for `vec`.
- Introduce `destruct_or{?,!}` to repeatedly destruct disjunctions in
  assumptions. The tactic can also be provided an explicit assumption name;
  `destruct_and{?,!}` has been generalized accordingly and now can also be
  provided an explicit assumption name.
  Slight breaking change: `destruct_and` no longer handle `False`;
  `destruct_or` now handles `False` while `destruct_and` handles `True`,
  as the respective units of disjunction and conjunction.
- Add tactic `set_unfold in H`.
- Set `Hint Mode` for `TCAnd`, `TCOr`, `TCForall`, `TCForall2`, `TCElemOf`,
  `TCEq`, and `TCDiag`.
- Add type class `LookupTotal` with total lookup operation `(!!!) : M → K → A`.
  Provide instances for `list`, `fin_map`, and `vec`, as well as corresponding
  lemmas for the operations on these types. The instance for `vec` replaces the
  ad-hoc `!!!` definition. As a consequence, arguments of `!!!` are no longer
  parsed in `vec_scope` and `fin_scope`, respectively. Moreover, since `!!!`
  is overloaded, coercions around `!!!` no longer work.
- Make lemmas for `seq` and `seqZ` consistent:
  + Rename `fmap_seq` → `fmap_S_seq`
  + Add `fmap_add_seq`, and rename `seqZ_fmap` → `fmap_add_seqZ`
  + Rename `lookup_seq` → `lookup_seq_lt`
  + Rename `seqZ_lookup_lt` → `lookup_seqZ_lt`,
    `seqZ_lookup_ge` → `lookup_seqZ_ge`, and `seqZ_lookup` → `lookup_seqZ`
  + Rename `lookup_seq_inv` → `lookup_seq` and generalize it to a bi-implication
  + Add `NoDup_seqZ` and `Forall_seqZ`

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i '
s/\bdom_map_filter\b/dom_map_filter_subseteq/g
s/\bfmap_seq\b/fmap_S_seq/g
s/\bseqZ_fmap\b/fmap_add_seqZ/g
s/\blookup_seq\b/lookup_seq_lt/g
s/\blookup_seq_inv\b/lookup_seq/g
s/\bseqZ_lookup_lt\b/lookup_seqZ_lt/g
s/\bseqZ_lookup_ge\b/lookup_seqZ_ge/g
s/\bseqZ_lookup\b/lookup_seqZ/g
s/\bvec_to_list_of_list\b/vec_to_list_to_vec/g
s/\bfin_of_nat\b/nat_to_fin/g
s/\bfin_to_of_nat\b/fin_to_nat_to_fin/g
s/\bfin_of_to_nat\b/nat_to_fin_to_nat/g
' $(find theories -name "*.v")
```

## std++ 1.2.1 (released 2019-08-29)

This release of std++ received contributions by Dan Frumin, Michael Sammler,
Paolo G. Giarrusso, Paulo Emílio de Vilhena, Ralf Jung, Robbert Krebbers,
Rodolphe Lepigre, and Simon Spies.

Noteworthy additions and changes:

- Introduce `max` and `min` infix notations for `N` and `Z` like we have for `nat`.
- Make `solve_ndisj` tactic more powerful.
- Add type class `Involutive`.
- Improve `naive_solver` performance in case the goal is trivially solvable.
- Add a bunch of new lemmas for list, set, and map operations.
- Rename `lookup_imap` into `map_lookup_imap`.

## std++ 1.2.0 (released 2019-04-26)

Coq 8.9 is supported by this release, but Coq 8.6 is no longer supported. Use
std++ 1.1 if you have to use Coq 8.6. The repository moved to a new location at
https://gitlab.mpi-sws.org/iris/stdpp and automatically generated Coq-doc of
master is available at https://plv.mpi-sws.org/coqdoc/stdpp/.

This release of std++ received contributions by Dan Frumin, Hai Dang, Jan-Oliver
Kaiser, Mackie Loeffel, Maxime Dénès, Ralf Jung, Robbert Krebbers, and Tej
Chajed.

New features:

- New notations `=@{A}`, `≡@{A}`, `∈@{A}`, `∉@{A}`, `##@{A}`, `⊆@{A}`, `⊂@{A}`,
  `⊑@{A}`, `≡ₚ@{A}` for being explicit about the type.
- A definition of basic telescopes `tele` and some theory about them.
- A simple type class based canceler `NatCancel` for natural numbers.
- A type `binder` for anonymous and named binders to be used in program language
  definitions with string-based binders.
- More results about `set_fold` on sets and multisets.
- Notions of infinite and finite predicates/sets and basic theory about them.
- New operation `map_seq`.
- The symmetric and reflexive/transitive/symmetric closure of a relation (`sc`
  and `rtsc`, respectively).
- Different notions of confluence (diamond property, confluence, local
  confluence) and the relations between these.
- A `size` function for finite maps and prove some properties.
- More results about `Qp` fractions.
- More miscellaneous results about sets, maps, lists, multisets.
- Various type class utilities, e.g. `TCEq`, `TCIf`, `TCDiag`, `TCNoBackTrack`,
  and `tc_to_bool`.
- Generalize `gset_to_propset` to `set_to_propset` for any `SemiSet`.

Changes:

- Consistently use `lia` instead of `omega` everywhere.
- Consistently block `simpl` on all `Z` operations.
- The `Infinite` class is now defined using a function `fresh : list A → A`
  that given a list `xs`, gives an element `fresh xs ∉ xs`.
- Make `default` an abbreviation for `from_option id` (instead of just swapping
  the argument order of `from_option`).
- More efficient `Countable` instance for `list` that is linear instead of
  exponential.
- Improve performance of `set_solver` significantly by introducing specialized
  type class `SetUnfoldElemOf` for propositions involving `∈`.
- Make `gset` a `Definition` instead of a `Notation` to improve performance.
- Use `disj_union` (notation `⊎`) for disjoint union on multisets (that adds the
  multiplicities). Repurpose `∪` on multisets for the actual union (that takes
  the max of the multiplicities). 

Naming:

- Consistently use the `set` prefix instead of the `collection` prefix for
  definitions and lemmas.
- Renaming of classes:
  + `Collection` into `Set_` (`_` since `Set` is a reserved keyword)
  + `SimpleCollection` into `SemiSet`
  + `FinCollection` into `FinSet`
  + `CollectionMonad` into `MonadSet`
- Types:
  + `set A := A → Prop` into `propset`
  + `bset := A → bool` into `boolset`.
- Files:
  + `collections.v` into `sets.v`
  + `fin_collections.v` into `fin_sets.v`
  + `bset` into `boolset`
  + `set` into `propset`
- Consistently use the naming scheme `X_to_Y` for conversion functions, e.g.
  `list_to_map` instead of the former `map_of_list`.

The following `sed` script should perform most of the renaming:

```
sed '
s/SimpleCollection/SemiSet/g;
s/FinCollection/FinSet/g;
s/CollectionMonad/MonadSet/g;
s/Collection/Set\_/g;
s/collection\_simple/set\_semi\_set/g;
s/fin\_collection/fin\_set/g;
s/collection\_monad\_simple/monad\_set\_semi\_set/g;
s/collection\_equiv/set\_equiv/g;
s/\bbset/boolset/g;
s/mkBSet/BoolSet/g;
s/mkSet/PropSet/g;
s/set\_equivalence/set\_equiv\_equivalence/g;
s/collection\_subseteq/set\_subseteq/g;
s/collection\_disjoint/set\_disjoint/g;
s/collection\_fold/set\_fold/g;
s/collection\_map/set\_map/g;
s/collection\_size/set\_size/g;
s/collection\_filter/set\_filter/g;
s/collection\_guard/set\_guard/g;
s/collection\_choose/set\_choose/g;
s/collection\_ind/set\_ind/g;
s/collection\_wf/set\_wf/g;
s/map\_to\_collection/map\_to\_set/g;
s/map\_of\_collection/set\_to\_map/g;
s/map\_of\_list/list\_to\_map/g;
s/map\_of\_to_list/list\_to\_map\_to\_list/g;
s/map\_to\_of\_list/map\_to\_list\_to\_map/g;
s/\bof\_list/list\_to\_set/g;
s/\bof\_option/option\_to\_set/g;
s/elem\_of\_of\_list/elem\_of\_list\_to\_set/g;
s/elem\_of\_of\_option/elem\_of\_option\_to\_set/g;
s/collection\_not\_subset\_inv/set\_not\_subset\_inv/g;
s/seq\_set/set\_seq/g;
s/collections/sets/g;
s/collection/set/g;
s/to\_gmap/gset\_to\_gmap/g;
s/of\_bools/bools\_to\_natset/g;
s/to_bools/natset\_to\_bools/g;
s/coPset\.of_gset/gset\_to\_coPset/g;
s/coPset\.elem\_of\_of\_gset/elem\_of\_gset\_to\_coPset/g;
s/of\_gset\_finite/gset\_to\_coPset\_finite/g;
s/set\_seq\_S\_disjoint/set\_seq\_S\_end\_disjoint/g;
s/set\_seq\_S\_union/set\_seq\_S\_end\_union/g;
s/map\_to\_of\_list/map\_to\_list\_to\_map/g;
s/of\_bools/bools\_to\_natset/g;
s/to\_bools/natset\_to\_bools/g;
' -i $(find -name "*.v")
```

## std++ 1.1.0 (released 2017-12-19)

Coq 8.5 is no longer supported by this release of std++.  Use std++ 1.0 if you
have to use Coq 8.5.

New features:

- Many new lemmas about lists, vectors, sets, maps.
- Equivalence proofs between std++ functions and their alternative in the the
  Coq standard library, e.g. `List.nth`, `List.NoDop`.
- Typeclass versions of the logical connectives and list predicates:
  `TCOr`, `TCAnd`, `TCTrue`, `TCForall`, `TCForall2`.
- A function `tc_opaque` to make definitions type class opaque.
- A type class `Infinite` for infinite types.
- A generic implementation to obtain fresh elements of infinite types.
- More theory about curry and uncurry functions on `gmap`.
- A generic `filter` and `zip_with` operation on finite maps.
- A type of generic trees for showing that arbitrary types are countable.

Changes:

- Get rid of `Automatic Coercions Import`, it is deprecated.
  Also get rid of `Set Asymmetric Patterns`.
- Various changes and improvements to `f_equiv` and `solve_proper`.
- `Hint Mode` is now set for all operational type classes to make instance
  search less likely to diverge.
- New type class `RelDecision` for decidable relations, and `EqDecision` is
  defined in terms of it. This class allows to set `Hint Mode` properly.
- Use the flag `assert` of `Arguments` to make it more robust.
- The functions `imap` and `imap2` on lists are defined so that they enjoy more
  definitional equalities.
- Theory about `fin` is moved to its own file `fin.v`.
- Rename `preserving` → `mono`.

Changes to notations:

- Operational type classes for lattice notations: `⊑`,`⊓`, `⊔`, `⊤` `⊥`.
- Replace `⊥` for disjointness with `##`, so that `⊥` can be used for the
  bottom lattice element.
- All notations are now in `stdpp_scope` with scope key `stdpp`
  (formerly `C_scope` and `C`).
- Higher precedence for `.1` and `.2` that is compatible with ssreflect.
- Various changes to monadic notations to improve compatibility with Mtac2:
  + Pattern matching notation for monadic bind `'pat ← x; y` where `pat` can
    be any Coq pattern.
  + Change the level of the do-notation.
  + `<$>` is left associative.
  + Notation `x ;; y` for `_ ← x; y`.

## History

Coq-std++ has originally been developed by Robbert Krebbers as part of his
formalization of the C programming language in his PhD thesis, called
[CH2O](http://robbertkrebbers.nl/thesis.html). After that, Coq-std++ has been
part of the [Iris project](http://iris-project.org), and has continued to be
developed by Robbert Krebbers, Ralf Jung, and Jacques Henri-Jourdan.
