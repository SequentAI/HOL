# Theory value modules

Loading a theory from source compiles its generated `FooTheory.sig` and
`FooTheory.sml`, reads `FooTheory.dat`, rebuilds every type, term and
theorem in it, and registers the theory: its place in the theory graph,
its types and constants in the kernel, its theorems in `DB`, and its
theory data. On Poly/ML runtimes with dependent modules, the loader can
save what a source load built in a module, and later loads in any
process started from the same saved state install it instead, repeating
only the registration.

## Canonical kernel ids

A kernel id is a name and an epoch. Constants defined in a session get
epochs from a process-wide counter, so the same constant can have
different ids in two processes, depending on what each did before.
Types and constants of a theory read from disk instead get epoch 0 the
first time their name is inserted in the process
(`KernelSig.insert_sealed`); the counter never produces 0. A loaded
theory's ids therefore depend only on its `.dat`, not on what else was
loaded or in what order.

The loader records which theories are canonical: those in the saved
state, and theories loaded with canonical ids whose parents are all
canonical. A theory defined in the session is not, and neither is a
theory loaded on top of one. Terms and theorems built while loading a
canonical theory mean the same thing in every process that shares the
saved state and has loaded the theory's ancestors, whatever the order.

A type or constant name gets epoch 0 at most once per process, whatever
`Context.restore` does, so two different types or constants never share an id.
Loaded theories are sealed as before, so they cannot be loaded again.

## What a module holds

A module is written by the process that exported the theory, when the
build tool asks for it (below), or else after the first source load of
a canonical theory. Either way it depends only on the saved state. It holds the theory's compiled
signature and initialised structure, and the theory's data as decoded
from its `.dat` (`TheoryReader.decoded`): its parents, types,
constants, theorems, sharing tables and theory data. Values shared with
other theories, such as their constants, are copied into it.

A later `Meta.load "FooTheory"` installs the signature where the source
loader compiles `FooTheory.sig`, loads the parents and other
dependencies listed in `FooTheory.uo` as usual, then replaces compiling
`FooTheory.sml` with the same registration steps in the same order
(`TheoryReader.register_decoded`, `Theory.record_metadata`,
`Theory.load_complete`) and only then binds the structure. Load hooks
and theory data run exactly as for a source load.

A module is used only when the theory's parents are canonical, the
structures the generated source refers to are bound as when it was
saved, the kernel is `stdknl` or `expknl`, and
`TheoryReader.load_thydata_fn` has its default value. Otherwise the
theory is loaded from source.

## Loader interface

A build tool enables modules after starting from its base state:

```sml
val enabled = Meta.configureTheoryModuleCache
  {directory = "/path/to/cache", base_state = "/path/to/bin/hol.state"};
```

It returns `false` when the runtime lacks dependent modules, the base
state is not in the process's saved-state hierarchy, or the directory is
unusable; loads then stay on source.

After exporting a theory, the build tool can write its module at once:

```sml
Meta.produceTheoryModule "/path/to/FooTheory.sml";
```

The theory's ids in the exporting process are not canonical: they were
minted while its script ran. So this decodes the exported `.dat` as a
loader would, in a copy of the context without the theory's own types
and constants (`KernelSig.with_reload` lets the decode reinsert them
although the theory is sealed), saves the module, and puts the live
context back. The module is the one a first loader would save. It does
nothing when the theory is not the current one, a second call in the
same process finds the ids no longer canonical, or modules are not
enabled.

## Cache entries

A module is named by the saved state's identity, the theory name and the
`.dat` hash written in `FooTheory.sml`, the same literals the source
loader identifies the theory by. Its `.ref` file holds the module's
SHA-1, computed when it is written, and the module file's status (size,
modification and change times, inode). A load rehashes the module only
when that status differs or the file changed within the last second.
Missing, corrupt or mismatched modules are loaded from source and
saved again. Once registration has started, errors propagate without
retrying from source.

Modules are runtime-specific local files, separate from the portable
`.dat`, `.sig` and `.sml` outputs. The directory can be deleted when no
load is writing to it.
