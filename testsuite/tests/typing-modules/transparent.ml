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
