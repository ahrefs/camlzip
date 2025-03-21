(***********************************************************************)
(*                                                                     *)
(*                         The CamlZip library                         *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

open Printf

let list_entry e =
  let t = Unix.localtime e.Zip.mtime in
  printf "%6d  %6d  %c  %04d-%02d-%02d %02d:%02d  %c  %s\n"
    e.Zip.uncompressed_size
    e.Zip.compressed_size
    (match e.Zip.methd with Zip.Stored -> 's' | Zip.Deflated -> 'd')
    (t.Unix.tm_year + 1900) (t.Unix.tm_mon + 1) t.Unix.tm_mday
    t.Unix.tm_hour t.Unix.tm_min
    (if e.Zip.is_directory then 'd' else ' ')
    e.Zip.filename;
  if e.Zip.comment <> "" then
    printf "        %s\n" e.Zip.comment

let list (module Impl: Zip.READER) zipfile =
  let ic = Impl.open_in zipfile in
  if Impl.comment ic <> "" then printf "%s\n" (Impl.comment ic);
  List.iter list_entry (Impl.entries ic);
  Impl.close_in ic

let extract_entry (type a) (module Impl: Zip.READER with type in_file = a) (ifile: a) e =
  print_string e.Zip.filename; print_newline();
  if e.Zip.is_directory then begin
    try
      Unix.mkdir e.Zip.filename 0o777
    with Unix.Unix_error(Unix.EEXIST, _, _) -> ()
  end else begin
    Impl.copy_entry_to_file ifile e e.Zip.filename
  end


let extract (module Impl: Zip.READER) zipfile =
  prerr_endline ("extract  " ^ zipfile);
  let ic = Impl.open_in zipfile in
  List.iter (extract_entry (module Impl) ic) (Impl.entries ic);
  Impl.close_in ic;
  prerr_endline "extract ic end"

let rec add_entry: type a. (module Zip.WRITER with type out_file = a) -> a -> string -> unit =
  fun (module Impl) oc file ->
    let s = Unix.stat file in
    match s.Unix.st_kind with
      Unix.S_REG ->
        printf "Adding file %s\n" file; flush stdout;
        Impl.copy_file_to_entry file oc ~mtime:s.Unix.st_mtime file
    | Unix.S_DIR ->
        printf "Adding directory %s\n" file; flush stdout;
        Impl.add_entry "" oc ~mtime:s.Unix.st_mtime
          (if Filename.check_suffix file "/" then file else file ^ "/");
        let d = Unix.opendir file in
        begin try
          while true do
            let e = Unix.readdir d in
            if e <> "." && e <> ".." then add_entry (module Impl) oc (Filename.concat file e)
          done
        with End_of_file -> ()
        end;
        Unix.closedir d
    | _ -> ()

let create (module Impl: Zip.WRITER) zipfile files =
  let oc = Impl.open_out zipfile in
  Array.iter (add_entry (module Impl) oc) files;
  Impl.close_out oc;
  prerr_endline "end create"


let append (module Impl: Zip.WRITER) zipfile files =
  let oc = Impl.open_update zipfile in
  Array.iter (add_entry (module Impl) oc) files;
  Impl.close_out oc

module In_channel: Zip.IN_CHANNEL = struct
  type t = {
    data : bytes;
    mutable pos : int;
  }

  let open_in filename =
    let ic = open_in_bin filename in
    let len = in_channel_length ic in
    let data = Bytes.create len in
    really_input ic data 0 len;
    close_in ic;
    { data; pos = 0 }

  let close_in _ = ()

  let input_byte t =
    if t.pos >= Bytes.length t.data then raise End_of_file
    else (
      let c = Bytes.get t.data t.pos in
      t.pos <- t.pos + 1;
      Char.code c)

  let input t buf ofs len =
    let available = Bytes.length t.data - t.pos in
    let to_read = min len available in
    Bytes.blit t.data t.pos buf ofs to_read;
    t.pos <- t.pos + to_read;
    to_read

  let really_input t buf ofs len =
    let rec loop total =
      if total >= len then ()
      else (
        let r = input t buf (ofs + total) (len - total) in
        if r = 0 then raise End_of_file else loop (total + r))
    in
    loop 0

  let length t = Int64.of_int (Bytes.length t.data)

  let pos t = Int64.of_int t.pos

  let seek t pos64 =
    let pos_int = Int64.to_int pos64 in
    if pos_int < 0 || pos_int > Bytes.length t.data then invalid_arg "BytesChannel.seek: position out of bounds"
    else t.pos <- pos_int

  let of_descr fd =
    let buffer = Buffer.create 1024 in
    let tmp = Bytes.create 1024 in
    let rec loop () =
      let read = Unix.read fd tmp 0 1024 in
      if read = 0 then ()
      else (
        Buffer.add_subbytes buffer tmp 0 read;
        loop ())
    in
    loop ();
    { data = Buffer.to_bytes buffer; pos = 0 }
end

(* Read the whole file to memory first, then read from memory *)
module Zip_mem_reader = Zip.Make_reader(In_channel)

(* Make all writes in memory, dumping to a file at the very end *)
module Zip_mem_writer = Zip.Make_writer(In_channel)(struct
type t = {
  filename: string;
  mutable buf: bytes;
  mutable pos: int;
}

let initial_size = 1024

let create_buffer () = Bytes.create initial_size

(* Ensure there is enough capacity in t.buf to add [extra] bytes.
   If not, a new larger buffer is allocated, the existing data is copied,
   and the channel's buffer is updated. *)
let ensure_capacity t extra =
  let required = t.pos + extra in
  if required > Bytes.length t.buf then begin
    let new_capacity = max (Bytes.length t.buf * 2) required in
    let new_buf = Bytes.create new_capacity in
    Bytes.blit t.buf 0 new_buf 0 t.pos;
    t.buf <- new_buf
  end

let open_out filename =
  { buf = create_buffer (); pos = 0; filename }

let output_byte t byte =
  ensure_capacity t 1;
  Bytes.set t.buf t.pos (Char.chr ((byte mod 256 + 256) mod 256));
  t.pos <- t.pos + 1

let output_string t s =
  let len = String.length s in
  ensure_capacity t len;
  String.iteri (fun i c ->
    Bytes.set t.buf (t.pos + i) c
  ) s;
  t.pos <- t.pos + len

let output_substring t s ofs len =
  if ofs < 0 || len < 0 || ofs + len > String.length s then
    invalid_arg "BytesOutChannel.output_substring: invalid substring bounds";
  ensure_capacity t len;
  for i = 0 to len - 1 do
    Bytes.set t.buf (t.pos + i) s.[ofs + i]
  done;
  t.pos <- t.pos + len

let output t src src_ofs len =
  if src_ofs < 0 || len < 0 || src_ofs + len > Bytes.length src then
    invalid_arg "BytesOutChannel.output: invalid bounds";
  ensure_capacity t len;
  Bytes.blit src src_ofs t.buf t.pos len;
  t.pos <- t.pos + len

let pos t = Int64.of_int t.pos

(* [seek] updates the current write position. If seeking beyond the current
   buffer size, a new buffer is allocated (with zeros in the new region)
   and the existing data is copied over. *)
let seek t pos64 =
  let new_pos = Int64.to_int pos64 in
  if new_pos < 0 then invalid_arg "BytesOutChannel.seek: negative position";
  if new_pos > Bytes.length t.buf then begin
    let new_buf = Bytes.create new_pos in
    Bytes.blit t.buf 0 new_buf 0 t.pos;
    t.buf <- new_buf;
  end;
  t.pos <- new_pos

(* For an in-memory channel nothing needs to be done to "close" it. *)
let close_out t =
  let oc = Stdlib.open_out t.filename in
  Stdlib.output oc t.buf 0 t.pos;
  Stdlib.close_out oc

(* Build a channel from a Unix file descriptor by reading its entire contents.
   The read data becomes the initial contents of the channel, and the position
   is set to the end of the data. *)
let of_descr fd =
  let buffer_size = 1024 in
  let tmp = Bytes.create buffer_size in
  let chunks = ref [] in
  let total = ref 0 in
  let rec loop () =
    let n = Unix.read fd tmp 0 buffer_size in
    if n = 0 then () else begin
      let chunk = Bytes.sub tmp 0 n in
      chunks := chunk :: !chunks;
      total := !total + n;
      loop ()
    end
  in
  loop ();
  let result = Bytes.create !total in
  let pos_ref = ref 0 in
  List.rev !chunks |> List.iter (fun chunk ->
    let len = Bytes.length chunk in
    Bytes.blit chunk 0 result !pos_ref len;
    pos_ref := !pos_ref + len
  );
  { buf = result; pos = !total; filename = "" }
end)


let usage() =
  prerr_string
{|Usage: 
  minizip t <zipfile>           show contents of <zipfile>
  minizip x <zipfile>           extract files from <zipfile>
  minizip c <zipfile> <file> .. create a <zipfile> with the given files
  minizip a <zipfile> <file> .. add the given files to <zipfile>
|};
  exit 2

let _ =
  if Array.length Sys.argv < 3 then usage();
  let zipfile, (module Reader: Zip.READER), (module Writer: Zip.WRITER) =
    match Sys.argv.(2) with
    | "-b" ->
      if Array.length Sys.argv < 4 then usage();
      3, (module Zip_mem_reader), (module Zip_mem_writer)
    | _ -> 2, (module Zip), (module Zip)
  in
  match Sys.argv.(1) with
    "t" -> list (module Reader) Sys.argv.(zipfile)
  | "x" -> extract (module Reader) Sys.argv.(zipfile)
  | "c" -> create (module Writer) Sys.argv.(zipfile)
                  (Array.sub Sys.argv (zipfile + 1) (Array.length Sys.argv - zipfile - 1))
  | "a" -> append (module Writer) Sys.argv.(zipfile)
                  (Array.sub Sys.argv (zipfile + 1) (Array.length Sys.argv - zipfile - 1))
  | _ -> usage()
