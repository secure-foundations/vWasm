(module
  (import "env" "g0" (global $g0 f32))
  (func (param f32) (result f32)
    (global.get $g0)
  )
)
