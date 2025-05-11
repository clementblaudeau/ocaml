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
module AttributeItem = X0 [@@dynamic_alias]
module AttributeIdent = X0 [@@dynamic_alias]
module AttributeIdent' = X0 [@@dynamic_alias]
module type DynamicAliasAttributeItem =
  sig
    module AttributeItem = X0 [@@dynamic_alias]
    module AttributeIdent = X0 [@@dynamic_alias]
  end
|}]


(** 2. Inference *)

(* Strengthening introduces dynamic aliases of module fields *)
module M = struct module X = struct end end
module M' = struct include M end
[%%expect {|
module M : sig module X : sig end end
module M' : sig module X = M.X [@@dynamic_alias]  end
|}]

(** 3. Subtyping *)

(* Dynamic aliases are a subtype of static ones *)
module X0 = struct end
module TestSub : sig module X1 = X0 end =
  struct module X1 = X0 [@@dynamic_alias] end
[%%expect{|
module X0 : sig end
module TestSub : sig module X1 = X0 end
|}]
