exception Timeout

let with_timeout timeout f =
  let result = ref None in
  let finished = Condition.create () in
  let guard = Mutex.create () in
  let set x =
    Mutex.lock guard;
    result := Some x;
    Mutex.unlock guard in
  Mutex.lock guard;
  let work () =
    let x = f () in
    set x;
    Condition.signal finished in
  let delay () =
    Thread.delay timeout;
    Condition.signal finished in
  let _task = Thread.create work () in
  let _wait = Thread.create delay () in
  Condition.wait finished guard;
  match !result with
  | None ->
    (* Thread.kill _task; *)
    raise Timeout
  | Some x ->
    (* Thread.kill _wait; *)
    x
