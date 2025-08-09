import Lake
open Lake DSL

package «lean-knk» where
  -- Additional configuration can go here

lean_lib KNK where

@[default_target]
lean_exe knk where
  root := `Main

