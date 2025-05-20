(* TEST
 expect;
*)

(** This file contains tests relative to static aliases (aka absent aliases) *)

(** 1. Parsing *)

(** Attributes for static aliases in module expressions and signatures. To test
    that the attribute is indeed taken into account (i.e. not just the fallback
    case of the inference), both attributes are added. Type inference always
    checks first for static aliases, then for dynamic ones (regardless of the
    written order). *)
module X0 = struct end
module AttributeItem   = X0 [@@static_alias]  [@@dynamic_alias]
module AttributeItem'  = X0 [@@dynamic_alias] [@@static_alias]
module AttributeIdent  = X0 [@static_alias]   [@dynamic_alias]
module AttributeIdent' = X0 [@dynamic_alias]  [@static_alias]
module[@static_alias] [@dynamic_alias] AttributeItem'' = X0
module[@dynamic_alias] [@static_alias] AttributeItem''' = X0
module type AttributeItem =
  sig
    module AttributeItem  = X0 [@@static_alias] [@@dynamic_alias]
    module AttributeItem' = X0 [@@dynamic_alias] [@@static_alias]
    module[@static_alias] [@dynamic_alias] AttributeIdent = X0
    module[@dynamic_alias] [@static_alias] AttributeIdent' = X0
  end
[%%expect {|
module X0 : sig end
module AttributeItem = X0
module AttributeItem' = X0
module AttributeIdent = X0
module AttributeIdent' = X0
module AttributeItem'' = X0
module AttributeItem''' = X0
module type AttributeItem =
  sig
    module AttributeItem = X0
    module AttributeItem' = X0
    module AttributeIdent = X0
    module AttributeIdent' = X0
  end
|}]
