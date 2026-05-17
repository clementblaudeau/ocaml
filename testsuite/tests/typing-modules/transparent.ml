(* TEST
 expect;
*)

(** This file contains tests relative to transparent signatures (aka dynamic
    aliases, aka present aliases) *)

(** 1. Parsing *)

(** Attributes for dynamic aliases in module expressions and signatures *)
module X0 = struct end
module AttributeItem = X0 [@@dynamic_alias]
module AttributeIdent = X0 [@dynamic_alias]
module[@dynamic_alias] AttributeIdent' = X0
module type DynamicAliasAttributeItem = sig
  module AttributeItem = X0 [@@dynamic_alias]
  module[@dynamic_alias] AttributeIdent = X0
end
[%%expect {|
module X0 : sig end
module AttributeItem : (= X0 :> _)
module AttributeIdent : (= X0 :> _)
module AttributeIdent' : (= X0 :> _)
module type DynamicAliasAttributeItem =
  sig
    module AttributeItem : (= X0 :> _)
    module AttributeIdent : (= X0 :> _)
  end
|}]


(** 2. Inference *)

(* Strengthening introduces dynamic aliases of module fields *)
module M = struct module X = struct end end
module M' = struct include M end
[%%expect {|
module M : sig module X : sig end end
module M' : sig module X : (= M.X :> _) end
|}]

(* Avoidance should introduce dynamic aliases *)
module X0 = struct end
module M = struct
  open (struct module X1 = X0 [@@dynamic_alias] end)
  module X2 = X1
end
[%%expect{|
module X0 : sig end
module M : sig module X2 : (= X0 :> _) end
|}]

(* Inference should preserve the "most local" name, not defer to the origin *)
module X0 = struct end
module X1 = X0 [@@dynamic_alias]
module X2 = X1 [@@dynamic_alias]
module X3 = X2 [@@dynamic_alias]
[%%expect{|
module X0 : sig end
module X1 : (= X0 :> _)
module X2 : (= X1 :> _)
module X3 : (= X2 :> _)
|}]

(* Invalid signatures should be rejected *)
module X0 = struct type t = A | B end
module type Valid_same      = (= X0 :> sig type t = X0.t = A | B end)
module type Valid_subtype   = (= X0 :> sig type t end)
module type Invalid         = (= X0 :> sig type u end)
[%%expect{|
module X0 : sig type t = A | B end
module type Valid_same = (= X0 :> sig type t = X0.t = A | B end)
module type Valid_subtype = (= X0 :> sig type t = X0.t end)
Line 4, characters 30-54:
4 | module type Invalid         = (= X0 :> sig type u end)
                                  ^^^^^^^^^^^^^^^^^^^^^^^^
Error: This transparent signature is invalid: the signature of "X0"
       is not a subtype of the provided signature:
       Modules do not match:
         (= X0 :> sig type t = X0.t = A | B end)
       is not included in
         sig type u end
       The type "u" is required but not provided
|}]

(* Inference and functors *)
module X0 = struct end
module F(Y: (= X0 :> _)) = Y
[%%expect{|
module X0 : sig end
module F : (Y : (= X0 :> _)) -> (= X0 :> _)
|}]


(** 3. Subtyping *)

(* Dynamic aliases are a subtype of static ones *)
module X0 = struct end
module TestSub : sig module X1 = X0 [@@static_alias] end =
  struct module X1 = X0 [@@dynamic_alias] end
[%%expect{|
module X0 : sig end
module TestSub : sig module X1 = X0 end
|}]

(* Static aliases are *not* a subtype of dynamic ones *)
module X0 = struct end
module TestSub : sig module X1 = X0 [@@dynamic_alias] end =
  struct module X1 = X0 [@@static_alias] end
[%%expect{|
module X0 : sig end
Line 3, characters 2-44:
3 |   struct module X1 = X0 [@@static_alias] end
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Signature mismatch:
       Modules do not match:
         sig module X1 = X0 end
       is not included in
         sig module X1 : (= X0 :> _) end
       In module "X1":
       Modules do not match:
         (module X0) [@static_alias]
       is not included in
         (= X0 :> _)
|}]

(* Dynamic aliases are a subtype of other dynamic aliases with equivalent
   paths (even with static aliases in the chain of equalities) *)
module X0 = struct end
module X1 = X0 [@dynamic_alias]
module X2 = X0 [@static_alias]
module TestSub_dynamic_alias_chain : sig module X3 = X1 [@@dynamic_alias] end =
struct module X3 = X2 [@dynamic_alias] end
[%%expect{|
module X0 : sig end
module X1 : (= X0 :> _)
module X2 = X0
module TestSub_dynamic_alias_chain : sig module X3 : (= X1 :> _) end
|}]

(* Dynamic aliasing information can be lost by subtyping *)
module X0 = struct type t = A | B let x = A end
module TestSub_lost_alias_abstract_type :
sig module X1 : sig type t end end =
  struct module X1 = X0 [@dynamic_alias] end
module TestSub_lost_alias_concrete_type :
sig module X1 : sig type t = X0.t = A | B end end =
  struct module X1 = X0 [@dynamic_alias] end
[%%expect{|
module X0 : sig type t = A | B val x : t end
module TestSub_lost_alias_abstract_type : sig module X1 : sig type t end end
module TestSub_lost_alias_concrete_type :
  sig module X1 : sig type t = X0.t = A | B end end
|}]

(* Loosing an alias forces strengthening *)
module X0 = struct type t = A | B let x = A end
module TestSub_functor_call =
  (functor (Y: sig module X1 : sig type t end end) -> Y)(struct
    module X1 = X0 [@dynamic_alias]
  end)
[%%expect{|
module X0 : sig type t = A | B val x : t end
module TestSub_functor_call : sig module X1 : sig type t = X0.t end end
|}]

(* Chain of aliases can be traversed by subtyping *)
module X0 = struct module X = struct type t end end
module X1 = struct module X = X0.X [@@dynamic_alias] end
module Test_Sub_Chain : sig module X : sig type t = X0.X.t end end = X1 [@@dynamic_alias]
[%%expect{|
module X0 : sig module X : sig type t end end
module X1 : sig module X : (= X0.X :> _) end
module Test_Sub_Chain : sig module X : sig type t = X0.X.t end end
|}]


(* Path normalization goes through aliases *)
module X0 = struct end
module XDyn1 = X0 [@@dynamic_alias]
module XDyn2 = X0 [@@dynamic_alias]
module type SDyn1 = sig module X = XDyn1 [@@dynamic_alias] end
module type SDyn2 = sig module X = XDyn2 [@@dynamic_alias] end
let sub_test_dyn : (module SDyn1) -> (module SDyn2) = fun x -> x
module XStat1 = X0 [@@static_alias]
module XStat2 = X0 [@@static_alias]
module type SStat1 = sig module X = XStat1 [@@static_alias] end
module type SStat2 = sig module X = XStat2 [@@static_alias] end
let sub_test_stat : (module SStat1) -> (module SStat2) = fun x -> x
[%%expect{|
module X0 : sig end
module XDyn1 : (= X0 :> _)
module XDyn2 : (= X0 :> _)
module type SDyn1 = sig module X : (= XDyn1 :> _) end
module type SDyn2 = sig module X : (= XDyn2 :> _) end
val sub_test_dyn : (module SDyn1) -> (module SDyn2) = <fun>
module XStat1 = X0
module XStat2 = X0
module type SStat1 = sig module X = XStat1 end
module type SStat2 = sig module X = XStat2 end
val sub_test_stat : (module SStat1) -> (module SStat2) = <fun>
|}]


(* Using named module types *)
module X0 = struct type t type u end
module type S1 = (= X0 :> sig type t type u end)
module M  : (= X0 :> sig type t type u end) = X0 [@dynamic_alias]
module M' : S1 = X0 [@dynamic_alias] (* should be the same as above *)
[%%expect{|
module X0 : sig type t type u end
module type S1 = (= X0 :> sig type t = X0.t type u = X0.u end)
module M : (= X0 :> sig type t = X0.t type u = X0.u end)
module M' : S1
|}]


(* Chains of transparent signatures *)
module X0 = struct end
module X1 : (= X0 :> _) = X0 [@dynamic_alias]
module X2 : (= X1 :> (= X0 :> _)) = X1 [@dynamic_alias]
module X2': (= X1 :> (= X0 :> _)) = X0 [@dynamic_alias]
[%%expect{|
module X0 : sig end
module X1 : (= X0 :> _)
module X2 : (= X1 :> sig end)
module X2' : (= X1 :> sig end)
|}]


(* Subtyping tests with explicit ascriptions - simple case *)
module X0 = struct end
module X1 : (= X0 :> _ ) = X0 [@dynamic_alias]
module X2 : (= X1 :> sig end ) = X0 [@dynamic_alias]
module X3 : (= X2 :> sig end ) = X1 [@dynamic_alias]
module X4 : (= X3 :> _ ) = X3 [@dynamic_alias]
[%%expect {|
module X0 : sig end
module X1 : (= X0 :> _)
module X2 : (= X1 :> sig end)
module X3 : (= X2 :> sig end)
module X4 : (= X3 :> _)
|}]

(* Subtyping tests with explicit ascriptions - chains of ascriptions *)
module X0 = struct end
module X1 = X0 [@dynamic_alias]
module X2 = X0 [@dynamic_alias]
module X3 : (= X2 :> (= X1 :> (= X2 :> _)) ) = X0 [@dynamic_alias]
module X4 : (= X1 :> (= X1 :> (= X2 :> _)) ) = X1 [@dynamic_alias]
module X5 : (= X0 :> (= X1 :> (= X2 :> _)) ) = X2 [@dynamic_alias]
[%%expect {|
module X0 : sig end
module X1 : (= X0 :> _)
module X2 : (= X0 :> _)
module X3 : (= X2 :> sig end)
module X4 : (= X1 :> sig end)
module X5 : (= X0 :> sig end)
|}]

(* Subtyping tests with explicit ascriptions - with some types *)
module X0 = struct type t end
module X1 : (= X0 :> _ ) = X0 [@dynamic_alias]
module X2 : (= X0 :> sig type t end ) = X0 [@dynamic_alias]
module X3 : (= X0 :> sig type t = X0.t end ) = X1 [@dynamic_alias]
module X4 : (= X0 :> sig type t = X3.t end ) = X1 [@dynamic_alias]
[%%expect {|
module X0 : sig type t end
module X1 : (= X0 :> _)
module X2 : (= X0 :> sig type t = X0.t end)
module X3 : (= X0 :> sig type t = X0.t end)
module X4 : (= X0 :> sig type t = X3.t end)
|}]


(* Subtyping : (=P :> _) < (=P :> S) and (= P :> S) < (=P :> _)*)
module X0 = struct type t end
module TestSub
    (Y: (= X0 :> sig type t end)) : (= X0 :> _) = Y
module TestSub'
    (Y: (= X0 :> _)) : (= X0 :> sig type t end) = Y
[%%expect{|
module X0 : sig type t end
module TestSub : (Y : (= X0 :> sig type t = X0.t end)) -> (= X0 :> _)
module TestSub' : (Y : (= X0 :> _)) -> (= X0 :> sig type t = X0.t end)
|}]


(* Subtyping: when S1 < S2, (=P :> S1) < (=P :> S2)*)
module X0 = struct type t type u end
module type S1 = (= X0 :> _)
module type S2 = (= X0 :> _)
module TestSub (Y: S1) : sig module Z : S2 end = struct module Z = Y end
module type S1 = (= X0 :> sig type t type u end)
module type S2 = (= X0 :> sig type t end)
module TestSub (Y: S1) : S2 = Y
[%%expect{|
module X0 : sig type t type u end
module type S1 = (= X0 :> _)
module type S2 = (= X0 :> _)
module TestSub : (Y : S1) -> sig module Z : S2 end
module type S1 = (= X0 :> sig type t = X0.t type u = X0.u end)
module type S2 = (= X0 :> sig type t = X0.t end)
module TestSub : (Y : S1) -> S2
|}]


(** Include a transparent signature *)
module X0 = struct type t = A | B let x = A end
module X1 : (= X0 :> _ ) = X0 [@dynamic_alias]
module X2 = struct include X1 let y : X0.t = x end
[%%expect {|
module X0 : sig type t = A | B val x : t end
module X1 : (= X0 :> _)
module X2 : sig type t = X0.t = A | B val x : t val y : X0.t end
|}]

(* extract_sig_open: opening a transparent module with explicit sig should
   work *)
module X0 = struct type t = A | B let x = A end
module X1 : (= X0 :> sig type t = X0.t = A | B val x : t end) =
  X0 [@dynamic_alias]
module X2 = struct
  open X1
  let y : t = x
end
module X3 = struct
  include X0
  let y : t = x
end
[%%expect {|
module X0 : sig type t = A | B val x : t end
module X1 : (= X0 :> sig type t = X0.t = A | B val x : t end)
module X2 : sig val y : X1.t end
module X3 : sig type t = X0.t = A | B val x : t val y : t end
|}]


(* Transparent ascription on module expressions fails for now: X0 is typed as a
   static alias *)
module X0 = struct type t = A | B let x = A end
module X1 = (X0 : (=X0 :> sig type t end))
module X2 = (X0 : (=X0 :> sig end))
[%%expect {|
module X0 : sig type t = A | B val x : t end
Line 2, characters 13-15:
2 | module X1 = (X0 : (=X0 :> sig type t end))
                 ^^
Error: Signature mismatch:
       Modules do not match:
         (module X0) [@static_alias]
       is not included in
         (= X0 :> sig type t = X0.t end)
Unexecuted phrases: 1 phrases did not execute due to an error
|}]

(** Invalid attributes throw an error. We test that the [@dynamic_alias]
   attribute throws an error if used:

   1. At a non aliasable positions (outside of a module field of a structure or
   a signature).

   2. With a non-aliasable path (or with something else than a path)

   Similar tests for the [@static_alias] attribute are in [static_aliases.ml]
*)

(* Attribute on a non-aliasable path (functor argument) *)
module X0 = struct end
module F (_:sig end) = struct end
module NonAliasablePath(Y:sig end) = struct
  module X1 = Y [@@dynamic_alias]
end
[%%expect {|
module X0 : sig end
module F : sig end -> sig end
Line 16, characters 14-15:
16 |   module X1 = Y [@@dynamic_alias]
                   ^
Error: Functor arguments and recursive modules (within the
       recursive definition), such as "Y", cannot be aliased
|}]

(* Attribute on a non-aliasable path (recursive module inside the recursive
   knot) *)
module rec X0 : sig end = struct end
and NonAliasablePath : sig end = struct
  module X1 = X0 [@@dynamic_alias]
end
[%%expect {|
Line 3, characters 14-16:
3 |   module X1 = X0 [@@dynamic_alias]
                  ^^
Error: Functor arguments and recursive modules (within the
       recursive definition), such as "X0", cannot be aliased
|}]

(* 4. Approximation *)

(* Recursive transparent signatures are refused *)
module rec X1 : (= X1 :> _) = struct end
[%%expect {|
Line 1, characters 16-27:
1 | module rec X1 : (= X1 :> _) = struct end
                    ^^^^^^^^^^^
Error: This module type is recursive. This use of the recursive module "X1"
       within its own definition makes the module type of "X1" depend on
       itself. Such recursive definitions of module types are not allowed.
|}]

(* Non recursive transparent signatures are accepted *)
module X0 = struct type t = A | B let x = A  end
module rec X1 : (= X0 :> sig type t val x : t end ) = X2.X
and X2 : sig module X : (= X0 :> _) end = struct module X = X0 [@@dynamic_alias] end
[%%expect {|
module X0 : sig type t = A | B val x : t end
module rec X1 : (= X0 :> sig type t = X0.t val x : t end)
and X2 : sig module X : (= X0 :> _) end
|}]


(* 5. Miscellaneous *)

(* Transparent aliases of functors *)
module F (X : sig type t end) = struct type u = X.t type v end
module G = F [@@dynamic_alias]
module X0 = struct type t end
module X1 : (= X0 :> _ ) = X0 [@dynamic_alias]
module R = G(struct type t = int end)
module S = G(X1)
[%%expect {|
module F : (X : sig type t end) -> sig type u = X.t type v end
module G : (= F :> _)
module X0 : sig type t end
module X1 : (= X0 :> _)
module R : sig type u = int type v end
module S : sig type u = X1.t type v = F(X1).v end
|}]

(* Transparent signatures in functor parameters *)
module X0 = struct type t = int end
module F (Y : sig module A : (= X0 :> _) end) = struct
  let f (x : Y.A.t) : X0.t = x
end
[%%expect {|
module X0 : sig type t = int end
module F :
  (Y : sig module A : (= X0 :> _) end) -> sig val f : Y.A.t -> X0.t end
|}]


(* Module type of *)
module X = struct type t end
module Y = struct module A = X module B = X [@@dynamic_alias] end (* WRONG *)
module type T = module type of Y
[%%expect {|
module X : sig type t end
module Y : sig module A = X module B : (= X :> _) end
module type T = sig module A = X module B = X end
|}]

(* Module type of with explicit transparent signature *)
module X0 = struct type t end
module Y = struct
  module A : (= X0 :> sig type t end) = X0 [@dynamic_alias]
end
module type T = module type of Y
[%%expect {|
module X0 : sig type t end
module Y : sig module A : (= X0 :> sig type t = X0.t end) end
module type T = sig module A : (= X0 :> sig type t = X0.t end) end
|}]


(** 6. Error cases *)

(* Non-alias cannot satisfy a transparent signature requirement *)
module X0 = struct end
module TestErr (Y : sig end) : (= X0 :> _) = Y
[%%expect{|
module X0 : sig end
Line 5, characters 45-46:
5 | module TestErr (Y : sig end) : (= X0 :> _) = Y
                                                 ^
Error: Signature mismatch:
       Modules do not match: sig end is not included in (= X0 :> _)
|}]

(* Different paths: (= P1 :> _) is not a subtype of (= P2 :> _) *)
module X0 = struct end
module X1 = struct end
module TestErr : (= X1 :> _) = X0 [@dynamic_alias]
[%%expect{|
module X0 : sig end
module X1 : sig end
Line 3, characters 31-33:
3 | module TestErr : (= X1 :> _) = X0 [@dynamic_alias]
                                   ^^
Error: Signature mismatch:
       Modules do not match: (= X0 :> _) is not included in (= X1 :> _)
|}]

(* Static alias with different path cannot satisfy transparent *)
module X0 = struct end
module X1 = struct end
module TestErr : sig module A : (= X1 :> _) end =
  struct module A = X0 end
[%%expect{|
module X0 : sig end
module X1 : sig end
Line 4, characters 2-26:
4 |   struct module A = X0 end
      ^^^^^^^^^^^^^^^^^^^^^^^^
Error: Signature mismatch:
       Modules do not match:
         sig module A = X0 end
       is not included in
         sig module A : (= X1 :> _) end
       In module "A":
       Modules do not match:
         (module X0) [@static_alias]
       is not included in
         (= X1 :> _)
|}]


(** 7. Interactions *)

(* First-class modules with transparent signatures *)
module X0 = struct type t = int end
module type S = (= X0 :> sig type t end)
let pack (m : (module S)) = m
let use (m : (module S)) =
  let module M = (val m) in
  (0 : M.t)
[%%expect{|
module X0 : sig type t = int end
module type S = (= X0 :> sig type t = X0.t end)
val pack : (module S) -> (module S) = <fun>
val use : (module S) -> X0.t = <fun>
|}]

(* Transparent downgrade: type equalities from identity survive *)
module X0 = struct type t = int end
module X1 : (= X0 :> sig type t end) = X0 [@dynamic_alias]
module TestDowngrade : sig type t = X0.t end = X1
[%%expect{|
module X0 : sig type t = int end
module X1 : (= X0 :> sig type t = X0.t end)
module TestDowngrade : sig type t = X0.t end
|}]

(* Include with explicit transparent signature *)
module X0 = struct type t = A | B let x = A end
module X1 : (= X0 :> sig type t = X0.t = A | B val x : t end) = X0 [@dynamic_alias]
module X2 = struct include X1 let y : X0.t = x end
[%%expect{|
module X0 : sig type t = A | B val x : t end
module X1 : (= X0 :> sig type t = X0.t = A | B val x : t end)
module X2 : sig type t = X0.t = A | B val x : t val y : X0.t end
|}]

(* Functor returning a transparent signature *)
module X0 = struct type t end
module F (_ : sig end) : (= X0 :> _) = X0 [@dynamic_alias]
module R = F (struct end)
[%%expect{|
module X0 : sig type t end
Line 2, characters 39-41:
2 | module F (_ : sig end) : (= X0 :> _) = X0 [@dynamic_alias]
                                           ^^
Error: Signature mismatch:
       Modules do not match:
         sig type t = X0.t end
       is not included in
         (= X0 :> _)
Unexecuted phrases: 1 phrases did not execute due to an error
|}]


(** 8. remove_aliases_mty: transparent signatures survive in functor parameters *)

(* Static alias whose target has a transparent signature in the functor param.
   scrape_for_functor_arg resolves the static alias; the transparent signature
   it finds underneath should be left alone and still work. *)
module X0 = struct type t = int end
module X1 = X0 [@@dynamic_alias]
module Wrap = struct module A = X1 [@@dynamic_alias] end
module F (Y : sig module W = Wrap end) = struct
  type t = Y.W.A.t
  let f (x : t) : X0.t = x
end
[%%expect{|
module X0 : sig type t = int end
module X1 : (= X0 :> _)
module Wrap : sig module A : (= X1 :> _) end
module F :
  (Y : sig module W = Wrap end) -> sig type t = Y.W.A.t val f : t -> X0.t end
|}]

(* Transparent signature directly in a functor parameter should survive
   scrape_for_functor_arg and remain usable inside the functor body *)
module X0 = struct type t = int end
module X1 = X0 [@@dynamic_alias]
module F (Y : sig module A : (= X1 :> _) end) = struct
  type t = Y.A.t
  let f (x : t) : X0.t = x
end
module R = F (struct module A = X0 [@dynamic_alias] end)
[%%expect{|
module X0 : sig type t = int end
module X1 : (= X0 :> _)
module F :
  (Y : sig module A : (= X1 :> _) end) ->
    sig type t = Y.A.t val f : t -> X0.t end
module R : sig type t = int val f : t -> X0.t end
|}]


(* nondep_mty: functor result contains a transparent signature with an
   explicit sig, applied with an inline struct (no path) so nondep_supertype
   is called and must recurse through Mty_transparent(_, Some _). *)
module M = struct type t end
module F (X : sig end) : sig module A : (= M :> sig type t end) end =
  struct module A = M [@dynamic_alias] end
module R = F (struct end)
[%%expect{|
module M : sig type t end
module F : (X : sig end) -> sig module A : (= M :> sig type t = M.t end) end
module R : sig module A : (= M :> sig type t = M.t end) end
|}]


(* retrieve_functor_params: applying a non-functor with transparent sig.
   The error message path calls retrieve_functor_params on the module type,
   which must handle Mty_transparent(_, Some _) without crashing. *)
module X0 = struct type t end
module X1 : (= X0 :> sig type t end) = X0 [@dynamic_alias]
module R = X1 (struct end)
[%%expect{|
module X0 : sig type t end
module X1 : (= X0 :> sig type t = X0.t end)
Line 3, characters 11-26:
3 | module R = X1 (struct end)
               ^^^^^^^^^^^^^^^
Error: The module "X1" is not a functor, it cannot be applied.
|}]


(* Avoidance through a local open: X1/X2 are bound in a local struct that is
   opened, so they go out of scope at the end of [M]. Aliases [X3 = X1] and
   [X4 = X2] must be rewritten to reference X0 directly, for both static and
   dynamic aliases. *)
module M = struct
  module X0 = struct end
  open (struct
    module X1 = X0 [@static_alias]
    module X2 = X0 [@dynamic_alias]
  end)
  module X3 = X1 [@static_alias]
  module X4 = X2 [@dynamic_alias]
end
[%%expect{|
module M : sig module X0 : sig end module X3 = X0 module X4 : (= X0 :> _) end
|}]
