open GT
open OCanren
open OCanren.Std
open Printf

let print_span span =
  let ms = Mtime.Span.to_ms span in
  if ms > 10000.0
  then printf "%10.0fs \n%!" (Mtime.Span.to_s span)
  else printf "%10.0fms\n%!" ms

let inputs0 =
  Stdlib.List.init 7 (fun n -> (string_of_int (n+1), Stdlib.List.init ((n+1)*100) (fun _ -> 0)) )
  |> Stdlib.List.map (fun (name, xs) -> (name, Std.list (!!) xs))



module Len = struct
(*  let rec lengtho x l =
    conde
      [ (x === Std.List.nil () &&& (l === Std.Nat.zero))
      ; (fresh (z t h)
          (x === Std.( % ) h t)
          (l === Std.Nat.succ z)
          (lengtho t z))
      ]*)
      let rec lengtho x l =
        conde
          [
      (*      (trace_list "A" x) &&&*)
            (x === Std.List.nil ()) &&&
      (*      (trace_list "B" x) &&&*)
            (l === Std.Nat.zero)
          ; Fresh.three (fun z t h ->
                delay (fun () ->
      (*            (trace_list "C" x) &&&*)
                  (x === Std.( % ) h t) &&&
      (*            (trace_list "D" x) &&&*)

      (*            (trace_list "E" x) &&&*)

                  (l === Std.Nat.succ z) &&&
                  (lengtho t z)
      (*            (trace_list "F" x)*)
                ))
                ]

end

let () = Printexc.record_backtrace true

module LenBack = struct
  let trace_list msg x =
    trace1 msg x (fun fmt rr -> Format.fprintf fmt "%a" (GT.fmt Std.List.logic @@ (GT.fmt logic @@ GT.fmt GT.int))
      (rr#reify (Std.List.reify OCanren.reify)))

(*  let rec lengtho x l =
    conde
      [
(*        (trace_list "A" x) &&& *)
        (x === Std.List.nil ()) &&&
(*        (trace_list "B" x) &&& *)
        (l === Std.Nat.zero)
(*        &&&  (trace_list "D" x)*)
      ; (fresh (z t h)
(*            (trace_list "C" x)*)
            (x === Std.( % ) h t)
            (lengtho t z)
            (l === Std.Nat.succ z))
      ]*)

let rec lengtho x l =
  conde
    [
(*      (trace_list "A" x) &&&*)
      (x === Std.List.nil ()) &&&
(*      (trace_list "B" x) &&&*)
      (l === Std.Nat.zero)
    ; Fresh.three (fun z t h ->
          delay (fun () ->
(*            (trace_list "C" x) &&&*)
            (x === Std.( % ) h t) &&&
(*            (trace_list "D" x) &&&*)

(*            (trace_list "E" x) &&&*)
            (lengtho t z)&&&
            (l === Std.Nat.succ z)
(*            (trace_list "F" x)*)
          ))
    ]
end


let work f lst  =
  let open Tester in


  let start = Mtime_clock.counter () in
  for i=1 to 100 do
(*    Printf.printf "PIZDA\n%!";*)
    let open OCanren  in
    let s = run q (f lst) (fun rr -> rr#prjc @@ Std.Nat.prjc (fun _ _ -> assert false)) in
(*    Printf.printf "%s %d\n%!" __FILE__ __LINE__;*)
(*    assert (Stream.(is_empty @@ tl s));*)
(*    Printf.printf "%s %d\n%!" __FILE__ __LINE__;*)

    let n = Std.Nat.to_int @@ Stream.hd s in
(*    Printf.printf "%d\n%!" n;*)
(*    assert (700 = n);*)
    ()
  done;
  let span = Mtime_clock.count start in
  print_span span

let () =
  let lst = Stdlib.List.nth inputs0 6 |> snd in
(*  let lst = Std.list (!!) [ 0 ; 0; 0; 0] in*)
(*  OCanren.clear_counters ();
  work Len.lengtho lst;
  OCanren.report_counters ();*)

  OCanren.clear_counters ();
  work LenBack.lengtho lst;
  OCanren.report_counters ();
  ()


