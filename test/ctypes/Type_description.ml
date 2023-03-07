open Ctypes
module Types(F:Ctypes.TYPE) =
  struct
    open F
    type ctypes1_point = [ `ctypes1_point ] structure
    let (ctypes1_point : [ `ctypes1_point ] structure typ) =
      structure "Ctypes1_point_s"
    let ctypes1_point_x = field ctypes1_point "x" uint32_t
    let ctypes1_point_y = field ctypes1_point "y" uint32_t
    let _ = seal ctypes1_point
  end
