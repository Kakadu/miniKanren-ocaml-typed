(*
 * OCanren PPX
 * Copyright (C) 2016-2019
 *   Dmitrii Kosarev aka Kakadu
 * St.Petersburg State University, JetBrains Research
 *)

(* There we register two syntax extension to be runned together (to speedup compilation)
 * (actual extensions are provided via linking options)
 *)

let () = Ppxlib.Driver.standalone ()
