module Semantics.Common.FunctionInfo

type fn_info = {
  arg_count: nat;
  ret_count: (n:nat{n <= 1});
}
