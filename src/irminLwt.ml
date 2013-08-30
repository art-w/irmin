(*
 * Copyright (c) 2013 Thomas Gazagnaire <thomas@gazagnaire.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Lwt
open IrminTypes

module Key   = IrminKey.SHA1
module Value = IrminValue.Make(Key)(IrminValue.Blob(Key))
module Tag   = IrminTag

module C = struct
  module Key = Key
  module Value = Value
  module Tag = Tag
end

module Client = IrminRemote.Client(C)
module Memory = IrminMemory.Make(C)
module Disk = IrminDisk.Make(C)
module Mix: STORE = struct
  module C = C
  module Key_store = Memory.Key_store
  module Value_store = Disk.Value_store
  module Tag_store = Disk.Tag_store
  type t = {
    key  : Memory.Key_store.t;
    value: Disk.Value_store.t;
    tag  : Disk.Tag_store.t;
  }
  let key_store t = t.key
  let value_store t = t.value
  let tag_store t = t.tag
end

module MemoryServer = IrminRemote.Server(Memory)
module DiskServer   = IrminRemote.Server(Disk)
module MixServer    = IrminRemote.Server(Mix)
