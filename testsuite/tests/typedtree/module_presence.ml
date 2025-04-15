(* TEST
 flags = "-dtypedtree";
 expect;
*)

module X = struct end
[%%expect{|
[
  structure_item ([1,45+0]..[1,45+21])
    Tstr_module (Present)
    X/281
      module_expr ([1,45+11]..[1,45+21])
        Tmod_structure
        []
]

module X : sig end
|}]

module Y = X
[%%expect{|
[
  structure_item ([1,258+0]..[1,258+12])
    Tstr_module (Absent)
    Y/282
      module_expr ([1,258+11]..[1,258+12])
        Tmod_ident "X/281"
]

module Y = X
|}]

module type T = sig module Y = X end
[%%expect{|
[
  structure_item ([1,452+0]..[1,452+36])
    Tstr_modtype "T/284"
      module_type ([1,452+16]..[1,452+36])
        Tmty_signature
        [
          signature_item ([1,452+20]..[1,452+32])
            Tsig_module "Y/283" (Absent)
            module_type ([1,452+31]..[1,452+32])
              Tmty_alias "X/281"
        ]
]

module type T = sig module Y = X end
|}]
