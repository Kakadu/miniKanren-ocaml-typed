(* There we register two syntax extension to be runned together (to speedup compilation) *)
(* fresh *)
(* let () = Smart_logger.register () *)

(* REPR constructor for testing *)
(* let () = Ppx_repr.register () *)


let () = Ppxlib.Driver.standalone ()
