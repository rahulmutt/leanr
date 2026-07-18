prelude

namespace A
namespace B
end B
end A
open A B
open Foo (bar)
open Foo hiding baz
open Foo renaming a -> b
