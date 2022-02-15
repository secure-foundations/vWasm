open Prims
let (decode32_bounded_integer_1 : unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun b ->
    let last = FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
    let first =
      FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_zero)
        (FStar_UInt32.uint_to_t Prims.int_zero) in
    let n = FStar_UInt32.uint_to_t Prims.int_zero in
    let blast = FStar_Int_Cast.uint8_to_uint32 last in
    FStar_UInt32.add blast
      (FStar_UInt32.mul n (FStar_UInt32.uint_to_t (Prims.of_int (256))))
let (decode32_bounded_integer_2 : unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun b ->
    let last = FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_one) in
    let first =
      FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_zero)
        (FStar_UInt32.uint_to_t Prims.int_one) in
    let n =
      let last1 =
        FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
      let first1 =
        FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_zero)
          (FStar_UInt32.uint_to_t Prims.int_zero) in
      let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
      let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
      FStar_UInt32.add blast
        (FStar_UInt32.mul n1 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
    let blast = FStar_Int_Cast.uint8_to_uint32 last in
    FStar_UInt32.add blast
      (FStar_UInt32.mul n (FStar_UInt32.uint_to_t (Prims.of_int (256))))
let (decode32_bounded_integer_3 : unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun b ->
    let last = FStar_Bytes.get b (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
    let first =
      FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_zero)
        (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
    let n =
      let last1 =
        FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_one) in
      let first1 =
        FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_zero)
          (FStar_UInt32.uint_to_t Prims.int_one) in
      let n1 =
        let last2 =
          FStar_Bytes.get first1 (FStar_UInt32.uint_to_t Prims.int_zero) in
        let first2 =
          FStar_Bytes.slice first1 (FStar_UInt32.uint_to_t Prims.int_zero)
            (FStar_UInt32.uint_to_t Prims.int_zero) in
        let n2 = FStar_UInt32.uint_to_t Prims.int_zero in
        let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
        FStar_UInt32.add blast
          (FStar_UInt32.mul n2 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
      let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
      FStar_UInt32.add blast
        (FStar_UInt32.mul n1 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
    let blast = FStar_Int_Cast.uint8_to_uint32 last in
    FStar_UInt32.add blast
      (FStar_UInt32.mul n (FStar_UInt32.uint_to_t (Prims.of_int (256))))
let (decode32_bounded_integer_4 : unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun b ->
    let last = FStar_Bytes.get b (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
    let first =
      FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_zero)
        (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
    let n =
      let last1 =
        FStar_Bytes.get first (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
      let first1 =
        FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_zero)
          (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
      let n1 =
        let last2 =
          FStar_Bytes.get first1 (FStar_UInt32.uint_to_t Prims.int_one) in
        let first2 =
          FStar_Bytes.slice first1 (FStar_UInt32.uint_to_t Prims.int_zero)
            (FStar_UInt32.uint_to_t Prims.int_one) in
        let n2 =
          let last3 =
            FStar_Bytes.get first2 (FStar_UInt32.uint_to_t Prims.int_zero) in
          let first3 =
            FStar_Bytes.slice first2 (FStar_UInt32.uint_to_t Prims.int_zero)
              (FStar_UInt32.uint_to_t Prims.int_zero) in
          let n3 = FStar_UInt32.uint_to_t Prims.int_zero in
          let blast = FStar_Int_Cast.uint8_to_uint32 last3 in
          FStar_UInt32.add blast
            (FStar_UInt32.mul n3
               (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
        let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
        FStar_UInt32.add blast
          (FStar_UInt32.mul n2 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
      let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
      FStar_UInt32.add blast
        (FStar_UInt32.mul n1 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
    let blast = FStar_Int_Cast.uint8_to_uint32 last in
    FStar_UInt32.add blast
      (FStar_UInt32.mul n (FStar_UInt32.uint_to_t (Prims.of_int (256))))
let (decode32_bounded_integer :
  LowParse_Spec_BoundedInt.integer_size ->
    unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun sz ->
    match sz with
    | uu___ when uu___ = Prims.int_one ->
        (fun b ->
           let last =
             FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t Prims.int_zero) in
           let n = FStar_UInt32.uint_to_t Prims.int_zero in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
    | uu___ when uu___ = (Prims.of_int (2)) ->
        (fun b ->
           let last =
             FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_one) in
           let first =
             FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t Prims.int_one) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
             let first1 =
               FStar_Bytes.slice first
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t Prims.int_zero) in
             let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
    | uu___ when uu___ = (Prims.of_int (3)) ->
        (fun b ->
           let last =
             FStar_Bytes.get b (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
           let first =
             FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_one) in
             let first1 =
               FStar_Bytes.slice first
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t Prims.int_one) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t Prims.int_zero) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_zero)
                   (FStar_UInt32.uint_to_t Prims.int_zero) in
               let n2 = FStar_UInt32.uint_to_t Prims.int_zero in
               let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
               FStar_UInt32.add blast
                 (FStar_UInt32.mul n2
                    (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
    | uu___ when uu___ = (Prims.of_int (4)) ->
        (fun b ->
           let last =
             FStar_Bytes.get b (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
           let first =
             FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
           let n =
             let last1 =
               FStar_Bytes.get first
                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
             let first1 =
               FStar_Bytes.slice first
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t Prims.int_one) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_zero)
                   (FStar_UInt32.uint_to_t Prims.int_one) in
               let n2 =
                 let last3 =
                   FStar_Bytes.get first2
                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                 let first3 =
                   FStar_Bytes.slice first2
                     (FStar_UInt32.uint_to_t Prims.int_zero)
                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                 let n3 = FStar_UInt32.uint_to_t Prims.int_zero in
                 let blast = FStar_Int_Cast.uint8_to_uint32 last3 in
                 FStar_UInt32.add blast
                   (FStar_UInt32.mul n3
                      (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
               let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
               FStar_UInt32.add blast
                 (FStar_UInt32.mul n2
                    (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
let (parse32_bounded_integer' :
  LowParse_Spec_BoundedInt.integer_size ->
    LowParse_SLow_Base.bytes32 ->
      (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun sz ->
    fun input ->
      if FStar_UInt32.lt (FStar_Bytes.len input) (FStar_UInt32.uint_to_t sz)
      then FStar_Pervasives_Native.None
      else
        (let s' =
           FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
             (FStar_UInt32.uint_to_t sz) in
         FStar_Pervasives_Native.Some
           ((match sz with
             | uu___1 when uu___1 = Prims.int_one ->
                 FStar_UInt32.add
                   (FStar_Int_Cast.uint8_to_uint32
                      (FStar_Bytes.get s'
                         (FStar_UInt32.uint_to_t Prims.int_zero)))
                   (FStar_UInt32.mul (FStar_UInt32.uint_to_t Prims.int_zero)
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))
             | uu___1 when uu___1 = (Prims.of_int (2)) ->
                 FStar_UInt32.add
                   (FStar_Int_Cast.uint8_to_uint32
                      (FStar_Bytes.get s'
                         (FStar_UInt32.uint_to_t Prims.int_one)))
                   (FStar_UInt32.mul
                      (FStar_UInt32.add
                         (FStar_Int_Cast.uint8_to_uint32
                            (FStar_Bytes.get
                               (FStar_Bytes.slice s'
                                  (FStar_UInt32.uint_to_t Prims.int_zero)
                                  (FStar_UInt32.uint_to_t Prims.int_one))
                               (FStar_UInt32.uint_to_t Prims.int_zero)))
                         (FStar_UInt32.mul
                            (FStar_UInt32.uint_to_t Prims.int_zero)
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))
             | uu___1 when uu___1 = (Prims.of_int (3)) ->
                 FStar_UInt32.add
                   (FStar_Int_Cast.uint8_to_uint32
                      (FStar_Bytes.get s'
                         (FStar_UInt32.uint_to_t (Prims.of_int (2)))))
                   (FStar_UInt32.mul
                      (FStar_UInt32.add
                         (FStar_Int_Cast.uint8_to_uint32
                            (FStar_Bytes.get
                               (FStar_Bytes.slice s'
                                  (FStar_UInt32.uint_to_t Prims.int_zero)
                                  (FStar_UInt32.uint_to_t (Prims.of_int (2))))
                               (FStar_UInt32.uint_to_t Prims.int_one)))
                         (FStar_UInt32.mul
                            (FStar_UInt32.add
                               (FStar_Int_Cast.uint8_to_uint32
                                  (FStar_Bytes.get
                                     (FStar_Bytes.slice
                                        (FStar_Bytes.slice s'
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (2))))
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)
                                        (FStar_UInt32.uint_to_t Prims.int_one))
                                     (FStar_UInt32.uint_to_t Prims.int_zero)))
                               (FStar_UInt32.mul
                                  (FStar_UInt32.uint_to_t Prims.int_zero)
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))))
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))
             | uu___1 when uu___1 = (Prims.of_int (4)) ->
                 FStar_UInt32.add
                   (FStar_Int_Cast.uint8_to_uint32
                      (FStar_Bytes.get s'
                         (FStar_UInt32.uint_to_t (Prims.of_int (3)))))
                   (FStar_UInt32.mul
                      (FStar_UInt32.add
                         (FStar_Int_Cast.uint8_to_uint32
                            (FStar_Bytes.get
                               (FStar_Bytes.slice s'
                                  (FStar_UInt32.uint_to_t Prims.int_zero)
                                  (FStar_UInt32.uint_to_t (Prims.of_int (3))))
                               (FStar_UInt32.uint_to_t (Prims.of_int (2)))))
                         (FStar_UInt32.mul
                            (FStar_UInt32.add
                               (FStar_Int_Cast.uint8_to_uint32
                                  (FStar_Bytes.get
                                     (FStar_Bytes.slice
                                        (FStar_Bytes.slice s'
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (3))))
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (2))))
                                     (FStar_UInt32.uint_to_t Prims.int_one)))
                               (FStar_UInt32.mul
                                  (FStar_UInt32.add
                                     (FStar_Int_Cast.uint8_to_uint32
                                        (FStar_Bytes.get
                                           (FStar_Bytes.slice
                                              (FStar_Bytes.slice
                                                 (FStar_Bytes.slice s'
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)
                                                    (FStar_UInt32.uint_to_t
                                                       (Prims.of_int (3))))
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (2))))
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero)
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_one))
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)))
                                     (FStar_UInt32.mul
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (256)))))
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))))
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
             (FStar_UInt32.uint_to_t sz)))
let (parse32_bounded_integer_1 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t Prims.int_one)
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t Prims.int_one) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t Prims.int_zero) in
           let n = FStar_UInt32.uint_to_t Prims.int_zero in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t Prims.int_one)))
let (parse32_bounded_integer_2 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (2)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_one) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t Prims.int_one) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
             let first1 =
               FStar_Bytes.slice first
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t Prims.int_zero) in
             let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t (Prims.of_int (2)))))
let (parse32_bounded_integer_3 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (3)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_one) in
             let first1 =
               FStar_Bytes.slice first
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t Prims.int_one) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t Prims.int_zero) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_zero)
                   (FStar_UInt32.uint_to_t Prims.int_zero) in
               let n2 = FStar_UInt32.uint_to_t Prims.int_zero in
               let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
               FStar_UInt32.add blast
                 (FStar_UInt32.mul n2
                    (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t (Prims.of_int (3)))))
let (parse32_bounded_integer_4 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (4)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
           let n =
             let last1 =
               FStar_Bytes.get first
                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
             let first1 =
               FStar_Bytes.slice first
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t Prims.int_one) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_zero)
                   (FStar_UInt32.uint_to_t Prims.int_one) in
               let n2 =
                 let last3 =
                   FStar_Bytes.get first2
                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                 let first3 =
                   FStar_Bytes.slice first2
                     (FStar_UInt32.uint_to_t Prims.int_zero)
                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                 let n3 = FStar_UInt32.uint_to_t Prims.int_zero in
                 let blast = FStar_Int_Cast.uint8_to_uint32 last3 in
                 FStar_UInt32.add blast
                   (FStar_UInt32.mul n3
                      (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
               let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
               FStar_UInt32.add blast
                 (FStar_UInt32.mul n2
                    (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t (Prims.of_int (4)))))
let (serialize32_bounded_integer_1 :
  FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let lo = FStar_Int_Cast.uint32_to_uint8 input in
    let hi =
      FStar_UInt32.div input (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi = FStar_Bytes.empty_bytes in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_hi seq_lo
let (serialize32_bounded_integer_2 :
  FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let lo = FStar_Int_Cast.uint32_to_uint8 input in
    let hi =
      FStar_UInt32.div input (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
      let hi1 =
        FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 = FStar_Bytes.empty_bytes in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_hi1 seq_lo in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_hi seq_lo
let (serialize32_bounded_integer_3 :
  FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let lo = FStar_Int_Cast.uint32_to_uint8 input in
    let hi =
      FStar_UInt32.div input (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
      let hi1 =
        FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 =
        let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
        let hi2 =
          FStar_UInt32.div hi1 (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi2 = FStar_Bytes.empty_bytes in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
        FStar_Bytes.append seq_hi2 seq_lo in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_hi1 seq_lo in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_hi seq_lo
let (serialize32_bounded_integer_4 :
  FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let lo = FStar_Int_Cast.uint32_to_uint8 input in
    let hi =
      FStar_UInt32.div input (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
      let hi1 =
        FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 =
        let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
        let hi2 =
          FStar_UInt32.div hi1 (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi2 =
          let lo3 = FStar_Int_Cast.uint32_to_uint8 hi2 in
          let hi3 =
            FStar_UInt32.div hi2
              (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi3 = FStar_Bytes.empty_bytes in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo3 in
          FStar_Bytes.append seq_hi3 seq_lo in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
        FStar_Bytes.append seq_hi2 seq_lo in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_hi1 seq_lo in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_hi seq_lo
let (bounded_integer_of_le_32_1 : unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun b ->
    let last = FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
    let first =
      FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_one)
        (FStar_UInt32.uint_to_t Prims.int_one) in
    let n = FStar_UInt32.uint_to_t Prims.int_zero in
    let blast = FStar_Int_Cast.uint8_to_uint32 last in
    FStar_UInt32.add blast
      (FStar_UInt32.mul n (FStar_UInt32.uint_to_t (Prims.of_int (256))))
let (bounded_integer_of_le_32_2 : unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun b ->
    let last = FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
    let first =
      FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_one)
        (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
    let n =
      let last1 =
        FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
      let first1 =
        FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
          (FStar_UInt32.uint_to_t Prims.int_one) in
      let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
      let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
      FStar_UInt32.add blast
        (FStar_UInt32.mul n1 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
    let blast = FStar_Int_Cast.uint8_to_uint32 last in
    FStar_UInt32.add blast
      (FStar_UInt32.mul n (FStar_UInt32.uint_to_t (Prims.of_int (256))))
let (bounded_integer_of_le_32_3 : unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun b ->
    let last = FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
    let first =
      FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_one)
        (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
    let n =
      let last1 =
        FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
      let first1 =
        FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
          (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
      let n1 =
        let last2 =
          FStar_Bytes.get first1 (FStar_UInt32.uint_to_t Prims.int_zero) in
        let first2 =
          FStar_Bytes.slice first1 (FStar_UInt32.uint_to_t Prims.int_one)
            (FStar_UInt32.uint_to_t Prims.int_one) in
        let n2 = FStar_UInt32.uint_to_t Prims.int_zero in
        let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
        FStar_UInt32.add blast
          (FStar_UInt32.mul n2 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
      let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
      FStar_UInt32.add blast
        (FStar_UInt32.mul n1 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
    let blast = FStar_Int_Cast.uint8_to_uint32 last in
    FStar_UInt32.add blast
      (FStar_UInt32.mul n (FStar_UInt32.uint_to_t (Prims.of_int (256))))
let (bounded_integer_of_le_32_4 : unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun b ->
    let last = FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
    let first =
      FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_one)
        (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
    let n =
      let last1 =
        FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
      let first1 =
        FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
          (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
      let n1 =
        let last2 =
          FStar_Bytes.get first1 (FStar_UInt32.uint_to_t Prims.int_zero) in
        let first2 =
          FStar_Bytes.slice first1 (FStar_UInt32.uint_to_t Prims.int_one)
            (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
        let n2 =
          let last3 =
            FStar_Bytes.get first2 (FStar_UInt32.uint_to_t Prims.int_zero) in
          let first3 =
            FStar_Bytes.slice first2 (FStar_UInt32.uint_to_t Prims.int_one)
              (FStar_UInt32.uint_to_t Prims.int_one) in
          let n3 = FStar_UInt32.uint_to_t Prims.int_zero in
          let blast = FStar_Int_Cast.uint8_to_uint32 last3 in
          FStar_UInt32.add blast
            (FStar_UInt32.mul n3
               (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
        let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
        FStar_UInt32.add blast
          (FStar_UInt32.mul n2 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
      let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
      FStar_UInt32.add blast
        (FStar_UInt32.mul n1 (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
    let blast = FStar_Int_Cast.uint8_to_uint32 last in
    FStar_UInt32.add blast
      (FStar_UInt32.mul n (FStar_UInt32.uint_to_t (Prims.of_int (256))))
let (bounded_integer_of_le_32 :
  LowParse_Spec_BoundedInt.integer_size ->
    unit FStar_Bytes.lbytes -> FStar_UInt32.t)
  =
  fun sz ->
    match sz with
    | uu___ when uu___ = Prims.int_one ->
        (fun b ->
           let last =
             FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_one)
               (FStar_UInt32.uint_to_t Prims.int_one) in
           let n = FStar_UInt32.uint_to_t Prims.int_zero in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
    | uu___ when uu___ = (Prims.of_int (2)) ->
        (fun b ->
           let last =
             FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_one)
               (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
             let first1 =
               FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
                 (FStar_UInt32.uint_to_t Prims.int_one) in
             let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
    | uu___ when uu___ = (Prims.of_int (3)) ->
        (fun b ->
           let last =
             FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_one)
               (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
             let first1 =
               FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t Prims.int_zero) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_UInt32.uint_to_t Prims.int_one) in
               let n2 = FStar_UInt32.uint_to_t Prims.int_zero in
               let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
               FStar_UInt32.add blast
                 (FStar_UInt32.mul n2
                    (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
    | uu___ when uu___ = (Prims.of_int (4)) ->
        (fun b ->
           let last =
             FStar_Bytes.get b (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice b (FStar_UInt32.uint_to_t Prims.int_one)
               (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
             let first1 =
               FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
                 (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t Prims.int_zero) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
               let n2 =
                 let last3 =
                   FStar_Bytes.get first2
                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                 let first3 =
                   FStar_Bytes.slice first2
                     (FStar_UInt32.uint_to_t Prims.int_one)
                     (FStar_UInt32.uint_to_t Prims.int_one) in
                 let n3 = FStar_UInt32.uint_to_t Prims.int_zero in
                 let blast = FStar_Int_Cast.uint8_to_uint32 last3 in
                 FStar_UInt32.add blast
                   (FStar_UInt32.mul n3
                      (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
               let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
               FStar_UInt32.add blast
                 (FStar_UInt32.mul n2
                    (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
let (parse32_bounded_integer_le' :
  LowParse_Spec_BoundedInt.integer_size ->
    LowParse_SLow_Base.bytes32 ->
      (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun sz ->
    fun input ->
      if FStar_UInt32.lt (FStar_Bytes.len input) (FStar_UInt32.uint_to_t sz)
      then FStar_Pervasives_Native.None
      else
        (let s' =
           FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
             (FStar_UInt32.uint_to_t sz) in
         FStar_Pervasives_Native.Some
           ((match sz with
             | uu___1 when uu___1 = Prims.int_one ->
                 FStar_UInt32.add
                   (FStar_Int_Cast.uint8_to_uint32
                      (FStar_Bytes.get s'
                         (FStar_UInt32.uint_to_t Prims.int_zero)))
                   (FStar_UInt32.mul (FStar_UInt32.uint_to_t Prims.int_zero)
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))
             | uu___1 when uu___1 = (Prims.of_int (2)) ->
                 FStar_UInt32.add
                   (FStar_Int_Cast.uint8_to_uint32
                      (FStar_Bytes.get s'
                         (FStar_UInt32.uint_to_t Prims.int_zero)))
                   (FStar_UInt32.mul
                      (FStar_UInt32.add
                         (FStar_Int_Cast.uint8_to_uint32
                            (FStar_Bytes.get
                               (FStar_Bytes.slice s'
                                  (FStar_UInt32.uint_to_t Prims.int_one)
                                  (FStar_UInt32.uint_to_t (Prims.of_int (2))))
                               (FStar_UInt32.uint_to_t Prims.int_zero)))
                         (FStar_UInt32.mul
                            (FStar_UInt32.uint_to_t Prims.int_zero)
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))
             | uu___1 when uu___1 = (Prims.of_int (3)) ->
                 FStar_UInt32.add
                   (FStar_Int_Cast.uint8_to_uint32
                      (FStar_Bytes.get s'
                         (FStar_UInt32.uint_to_t Prims.int_zero)))
                   (FStar_UInt32.mul
                      (FStar_UInt32.add
                         (FStar_Int_Cast.uint8_to_uint32
                            (FStar_Bytes.get
                               (FStar_Bytes.slice s'
                                  (FStar_UInt32.uint_to_t Prims.int_one)
                                  (FStar_UInt32.uint_to_t (Prims.of_int (3))))
                               (FStar_UInt32.uint_to_t Prims.int_zero)))
                         (FStar_UInt32.mul
                            (FStar_UInt32.add
                               (FStar_Int_Cast.uint8_to_uint32
                                  (FStar_Bytes.get
                                     (FStar_Bytes.slice
                                        (FStar_Bytes.slice s'
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_one)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (3))))
                                        (FStar_UInt32.uint_to_t Prims.int_one)
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (2))))
                                     (FStar_UInt32.uint_to_t Prims.int_zero)))
                               (FStar_UInt32.mul
                                  (FStar_UInt32.uint_to_t Prims.int_zero)
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))))
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))
             | uu___1 when uu___1 = (Prims.of_int (4)) ->
                 FStar_UInt32.add
                   (FStar_Int_Cast.uint8_to_uint32
                      (FStar_Bytes.get s'
                         (FStar_UInt32.uint_to_t Prims.int_zero)))
                   (FStar_UInt32.mul
                      (FStar_UInt32.add
                         (FStar_Int_Cast.uint8_to_uint32
                            (FStar_Bytes.get
                               (FStar_Bytes.slice s'
                                  (FStar_UInt32.uint_to_t Prims.int_one)
                                  (FStar_UInt32.uint_to_t (Prims.of_int (4))))
                               (FStar_UInt32.uint_to_t Prims.int_zero)))
                         (FStar_UInt32.mul
                            (FStar_UInt32.add
                               (FStar_Int_Cast.uint8_to_uint32
                                  (FStar_Bytes.get
                                     (FStar_Bytes.slice
                                        (FStar_Bytes.slice s'
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_one)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (4))))
                                        (FStar_UInt32.uint_to_t Prims.int_one)
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (3))))
                                     (FStar_UInt32.uint_to_t Prims.int_zero)))
                               (FStar_UInt32.mul
                                  (FStar_UInt32.add
                                     (FStar_Int_Cast.uint8_to_uint32
                                        (FStar_Bytes.get
                                           (FStar_Bytes.slice
                                              (FStar_Bytes.slice
                                                 (FStar_Bytes.slice s'
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_one)
                                                    (FStar_UInt32.uint_to_t
                                                       (Prims.of_int (4))))
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_one)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (3))))
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_one)
                                              (FStar_UInt32.uint_to_t
                                                 (Prims.of_int (2))))
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)))
                                     (FStar_UInt32.mul
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (256)))))
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))))
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
             (FStar_UInt32.uint_to_t sz)))
let (parse32_bounded_integer_le_1 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t Prims.int_one)
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t Prims.int_one) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_one)
               (FStar_UInt32.uint_to_t Prims.int_one) in
           let n = FStar_UInt32.uint_to_t Prims.int_zero in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t Prims.int_one)))
let (parse32_bounded_integer_le_2 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (2)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_one)
               (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
             let first1 =
               FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
                 (FStar_UInt32.uint_to_t Prims.int_one) in
             let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t (Prims.of_int (2)))))
let (parse32_bounded_integer_le_3 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (3)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_one)
               (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
             let first1 =
               FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t Prims.int_zero) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_UInt32.uint_to_t Prims.int_one) in
               let n2 = FStar_UInt32.uint_to_t Prims.int_zero in
               let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
               FStar_UInt32.add blast
                 (FStar_UInt32.mul n2
                    (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t (Prims.of_int (3)))))
let (parse32_bounded_integer_le_4 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (4)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_zero) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_one)
               (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
           let n =
             let last1 =
               FStar_Bytes.get first (FStar_UInt32.uint_to_t Prims.int_zero) in
             let first1 =
               FStar_Bytes.slice first (FStar_UInt32.uint_to_t Prims.int_one)
                 (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t Prims.int_zero) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
               let n2 =
                 let last3 =
                   FStar_Bytes.get first2
                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                 let first3 =
                   FStar_Bytes.slice first2
                     (FStar_UInt32.uint_to_t Prims.int_one)
                     (FStar_UInt32.uint_to_t Prims.int_one) in
                 let n3 = FStar_UInt32.uint_to_t Prims.int_zero in
                 let blast = FStar_Int_Cast.uint8_to_uint32 last3 in
                 FStar_UInt32.add blast
                   (FStar_UInt32.mul n3
                      (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
               let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
               FStar_UInt32.add blast
                 (FStar_UInt32.mul n2
                    (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
             FStar_UInt32.add blast
               (FStar_UInt32.mul n1
                  (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint32 last in
           FStar_UInt32.add blast
             (FStar_UInt32.mul n
                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t (Prims.of_int (4)))))
let (parse32_u16_le :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt16.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match if
            FStar_UInt32.lt (FStar_Bytes.len input)
              (FStar_UInt32.uint_to_t (Prims.of_int (2)))
          then FStar_Pervasives_Native.None
          else
            (let s' =
               FStar_Bytes.slice input
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
             FStar_Pervasives_Native.Some
               ((let last =
                   FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_zero) in
                 let first =
                   FStar_Bytes.slice s'
                     (FStar_UInt32.uint_to_t Prims.int_one)
                     (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                 let n =
                   let last1 =
                     FStar_Bytes.get first
                       (FStar_UInt32.uint_to_t Prims.int_zero) in
                   let first1 =
                     FStar_Bytes.slice first
                       (FStar_UInt32.uint_to_t Prims.int_one)
                       (FStar_UInt32.uint_to_t Prims.int_one) in
                   let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
                   let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                   FStar_UInt32.add blast
                     (FStar_UInt32.mul n1
                        (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
                 let blast = FStar_Int_Cast.uint8_to_uint32 last in
                 FStar_UInt32.add blast
                   (FStar_UInt32.mul n
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                 (FStar_UInt32.uint_to_t (Prims.of_int (2)))))
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          ((FStar_Int_Cast.uint32_to_uint16 v1), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (parse32_u32_le :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match if
            FStar_UInt32.lt (FStar_Bytes.len input)
              (FStar_UInt32.uint_to_t (Prims.of_int (4)))
          then FStar_Pervasives_Native.None
          else
            (let s' =
               FStar_Bytes.slice input
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
             FStar_Pervasives_Native.Some
               ((let last =
                   FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_zero) in
                 let first =
                   FStar_Bytes.slice s'
                     (FStar_UInt32.uint_to_t Prims.int_one)
                     (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                 let n =
                   let last1 =
                     FStar_Bytes.get first
                       (FStar_UInt32.uint_to_t Prims.int_zero) in
                   let first1 =
                     FStar_Bytes.slice first
                       (FStar_UInt32.uint_to_t Prims.int_one)
                       (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                   let n1 =
                     let last2 =
                       FStar_Bytes.get first1
                         (FStar_UInt32.uint_to_t Prims.int_zero) in
                     let first2 =
                       FStar_Bytes.slice first1
                         (FStar_UInt32.uint_to_t Prims.int_one)
                         (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                     let n2 =
                       let last3 =
                         FStar_Bytes.get first2
                           (FStar_UInt32.uint_to_t Prims.int_zero) in
                       let first3 =
                         FStar_Bytes.slice first2
                           (FStar_UInt32.uint_to_t Prims.int_one)
                           (FStar_UInt32.uint_to_t Prims.int_one) in
                       let n3 = FStar_UInt32.uint_to_t Prims.int_zero in
                       let blast = FStar_Int_Cast.uint8_to_uint32 last3 in
                       FStar_UInt32.add blast
                         (FStar_UInt32.mul n3
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
                     let blast = FStar_Int_Cast.uint8_to_uint32 last2 in
                     FStar_UInt32.add blast
                       (FStar_UInt32.mul n2
                          (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
                   let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                   FStar_UInt32.add blast
                     (FStar_UInt32.mul n1
                        (FStar_UInt32.uint_to_t (Prims.of_int (256)))) in
                 let blast = FStar_Int_Cast.uint8_to_uint32 last in
                 FStar_UInt32.add blast
                   (FStar_UInt32.mul n
                      (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                 (FStar_UInt32.uint_to_t (Prims.of_int (4)))))
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_bounded_integer_le_1 :
  FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let lo = FStar_Int_Cast.uint32_to_uint8 x in
    let hi = FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi = FStar_Bytes.empty_bytes in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_lo seq_hi
let (serialize32_bounded_integer_le_2 :
  FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let lo = FStar_Int_Cast.uint32_to_uint8 x in
    let hi = FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
      let hi1 =
        FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 = FStar_Bytes.empty_bytes in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_lo seq_hi1 in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_lo seq_hi
let (serialize32_bounded_integer_le_3 :
  FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let lo = FStar_Int_Cast.uint32_to_uint8 x in
    let hi = FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
      let hi1 =
        FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 =
        let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
        let hi2 =
          FStar_UInt32.div hi1 (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi2 = FStar_Bytes.empty_bytes in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
        FStar_Bytes.append seq_lo seq_hi2 in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_lo seq_hi1 in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_lo seq_hi
let (serialize32_bounded_integer_le_4 :
  FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let lo = FStar_Int_Cast.uint32_to_uint8 x in
    let hi = FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
      let hi1 =
        FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 =
        let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
        let hi2 =
          FStar_UInt32.div hi1 (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi2 =
          let lo3 = FStar_Int_Cast.uint32_to_uint8 hi2 in
          let hi3 =
            FStar_UInt32.div hi2
              (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi3 = FStar_Bytes.empty_bytes in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo3 in
          FStar_Bytes.append seq_lo seq_hi3 in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
        FStar_Bytes.append seq_lo seq_hi2 in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_lo seq_hi1 in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_lo seq_hi
let (serialize32_u16_le : FStar_UInt16.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = FStar_Int_Cast.uint16_to_uint32 input in
    let lo = FStar_Int_Cast.uint32_to_uint8 x in
    let hi = FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
      let hi1 =
        FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 = FStar_Bytes.empty_bytes in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_lo seq_hi1 in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_lo seq_hi
let (serialize32_u32_le : FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = input in
    let lo = FStar_Int_Cast.uint32_to_uint8 x in
    let hi = FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
      let hi1 =
        FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 =
        let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
        let hi2 =
          FStar_UInt32.div hi1 (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi2 =
          let lo3 = FStar_Int_Cast.uint32_to_uint8 hi2 in
          let hi3 =
            FStar_UInt32.div hi2
              (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi3 = FStar_Bytes.empty_bytes in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo3 in
          FStar_Bytes.append seq_lo seq_hi3 in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
        FStar_Bytes.append seq_lo seq_hi2 in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_lo seq_hi1 in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_lo seq_hi
let (size32_u16_le : FStar_UInt16.t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (2))
let (size32_u32_le : FStar_UInt32.t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))
let (parse32_bounded_int32' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        LowParse_SLow_Base.bytes32 ->
          (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min32 ->
    fun max32 ->
      fun sz32 ->
        fun input ->
          match match match FStar_UInt32.v sz32 with
                      | uu___ when uu___ = Prims.int_one ->
                          if
                            FStar_UInt32.lt (FStar_Bytes.len input)
                              (FStar_UInt32.uint_to_t Prims.int_one)
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              ((FStar_UInt32.add
                                  (FStar_Int_Cast.uint8_to_uint32
                                     (FStar_Bytes.get
                                        (FStar_Bytes.slice input
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_one))
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)))
                                  (FStar_UInt32.mul
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))),
                                (FStar_UInt32.uint_to_t Prims.int_one))
                      | uu___ when uu___ = (Prims.of_int (2)) ->
                          if
                            FStar_UInt32.lt (FStar_Bytes.len input)
                              (FStar_UInt32.uint_to_t (Prims.of_int (2)))
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              ((FStar_UInt32.add
                                  (FStar_Int_Cast.uint8_to_uint32
                                     (FStar_Bytes.get
                                        (FStar_Bytes.slice input
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (2))))
                                        (FStar_UInt32.uint_to_t Prims.int_one)))
                                  (FStar_UInt32.mul
                                     (FStar_UInt32.add
                                        (FStar_Int_Cast.uint8_to_uint32
                                           (FStar_Bytes.get
                                              (FStar_Bytes.slice
                                                 (FStar_Bytes.slice input
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)
                                                    (FStar_UInt32.uint_to_t
                                                       (Prims.of_int (2))))
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero)
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_one))
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero)))
                                        (FStar_UInt32.mul
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (256)))))
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))),
                                (FStar_UInt32.uint_to_t (Prims.of_int (2))))
                      | uu___ when uu___ = (Prims.of_int (3)) ->
                          if
                            FStar_UInt32.lt (FStar_Bytes.len input)
                              (FStar_UInt32.uint_to_t (Prims.of_int (3)))
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              ((FStar_UInt32.add
                                  (FStar_Int_Cast.uint8_to_uint32
                                     (FStar_Bytes.get
                                        (FStar_Bytes.slice input
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (3))))
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (2)))))
                                  (FStar_UInt32.mul
                                     (FStar_UInt32.add
                                        (FStar_Int_Cast.uint8_to_uint32
                                           (FStar_Bytes.get
                                              (FStar_Bytes.slice
                                                 (FStar_Bytes.slice input
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)
                                                    (FStar_UInt32.uint_to_t
                                                       (Prims.of_int (3))))
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (2))))
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_one)))
                                        (FStar_UInt32.mul
                                           (FStar_UInt32.add
                                              (FStar_Int_Cast.uint8_to_uint32
                                                 (FStar_Bytes.get
                                                    (FStar_Bytes.slice
                                                       (FStar_Bytes.slice
                                                          (FStar_Bytes.slice
                                                             input
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_zero)
                                                             (FStar_UInt32.uint_to_t
                                                                (Prims.of_int (3))))
                                                          (FStar_UInt32.uint_to_t
                                                             Prims.int_zero)
                                                          (FStar_UInt32.uint_to_t
                                                             (Prims.of_int (2))))
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_zero)
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_one))
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)))
                                              (FStar_UInt32.mul
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (256)))))
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (256)))))
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))),
                                (FStar_UInt32.uint_to_t (Prims.of_int (3))))
                      | uu___ when uu___ = (Prims.of_int (4)) ->
                          if
                            FStar_UInt32.lt (FStar_Bytes.len input)
                              (FStar_UInt32.uint_to_t (Prims.of_int (4)))
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              ((FStar_UInt32.add
                                  (FStar_Int_Cast.uint8_to_uint32
                                     (FStar_Bytes.get
                                        (FStar_Bytes.slice input
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (4))))
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (3)))))
                                  (FStar_UInt32.mul
                                     (FStar_UInt32.add
                                        (FStar_Int_Cast.uint8_to_uint32
                                           (FStar_Bytes.get
                                              (FStar_Bytes.slice
                                                 (FStar_Bytes.slice input
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)
                                                    (FStar_UInt32.uint_to_t
                                                       (Prims.of_int (4))))
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (3))))
                                              (FStar_UInt32.uint_to_t
                                                 (Prims.of_int (2)))))
                                        (FStar_UInt32.mul
                                           (FStar_UInt32.add
                                              (FStar_Int_Cast.uint8_to_uint32
                                                 (FStar_Bytes.get
                                                    (FStar_Bytes.slice
                                                       (FStar_Bytes.slice
                                                          (FStar_Bytes.slice
                                                             input
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_zero)
                                                             (FStar_UInt32.uint_to_t
                                                                (Prims.of_int (4))))
                                                          (FStar_UInt32.uint_to_t
                                                             Prims.int_zero)
                                                          (FStar_UInt32.uint_to_t
                                                             (Prims.of_int (3))))
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_zero)
                                                       (FStar_UInt32.uint_to_t
                                                          (Prims.of_int (2))))
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_one)))
                                              (FStar_UInt32.mul
                                                 (FStar_UInt32.add
                                                    (FStar_Int_Cast.uint8_to_uint32
                                                       (FStar_Bytes.get
                                                          (FStar_Bytes.slice
                                                             (FStar_Bytes.slice
                                                                (FStar_Bytes.slice
                                                                   (FStar_Bytes.slice
                                                                    input
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    (FStar_UInt32.uint_to_t
                                                                    (Prims.of_int (4))))
                                                                   (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                   (FStar_UInt32.uint_to_t
                                                                    (Prims.of_int (3))))
                                                                (FStar_UInt32.uint_to_t
                                                                   Prims.int_zero)
                                                                (FStar_UInt32.uint_to_t
                                                                   (Prims.of_int (2))))
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_zero)
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_one))
                                                          (FStar_UInt32.uint_to_t
                                                             Prims.int_zero)))
                                                    (FStar_UInt32.mul
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_zero)
                                                       (FStar_UInt32.uint_to_t
                                                          (Prims.of_int (256)))))
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (256)))))
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (256)))))
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))),
                                (FStar_UInt32.uint_to_t (Prims.of_int (4))))
                with
                | FStar_Pervasives_Native.Some (v, consumed) ->
                    if
                      Prims.op_Negation
                        ((FStar_UInt32.lt v min32) ||
                           (FStar_UInt32.lt max32 v))
                    then FStar_Pervasives_Native.Some (v, consumed)
                    else FStar_Pervasives_Native.None
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some (v1, consumed)
          | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t Prims.int_one)
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t Prims.int_one) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_zero)
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                           let n = FStar_UInt32.uint_to_t Prims.int_zero in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t Prims.int_one)))
              with
              | FStar_Pervasives_Native.Some (v, consumed) ->
                  if
                    Prims.op_Negation
                      ((FStar_UInt32.lt v min) || (FStar_UInt32.lt max v))
                  then FStar_Pervasives_Native.Some (v, consumed)
                  else FStar_Pervasives_Native.None
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v1, consumed) ->
            FStar_Pervasives_Native.Some (v1, consumed)
        | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t (Prims.of_int (2)))
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t Prims.int_one) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_zero)
                               (FStar_UInt32.uint_to_t Prims.int_one) in
                           let n =
                             let last1 =
                               FStar_Bytes.get first
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let first1 =
                               FStar_Bytes.slice first
                                 (FStar_UInt32.uint_to_t Prims.int_zero)
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
                             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                             FStar_UInt32.add blast
                               (FStar_UInt32.mul n1
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))) in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t (Prims.of_int (2)))))
              with
              | FStar_Pervasives_Native.Some (v, consumed) ->
                  if
                    Prims.op_Negation
                      ((FStar_UInt32.lt v min) || (FStar_UInt32.lt max v))
                  then FStar_Pervasives_Native.Some (v, consumed)
                  else FStar_Pervasives_Native.None
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v1, consumed) ->
            FStar_Pervasives_Native.Some (v1, consumed)
        | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t (Prims.of_int (3)))
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_zero)
                               (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                           let n =
                             let last1 =
                               FStar_Bytes.get first
                                 (FStar_UInt32.uint_to_t Prims.int_one) in
                             let first1 =
                               FStar_Bytes.slice first
                                 (FStar_UInt32.uint_to_t Prims.int_zero)
                                 (FStar_UInt32.uint_to_t Prims.int_one) in
                             let n1 =
                               let last2 =
                                 FStar_Bytes.get first1
                                   (FStar_UInt32.uint_to_t Prims.int_zero) in
                               let first2 =
                                 FStar_Bytes.slice first1
                                   (FStar_UInt32.uint_to_t Prims.int_zero)
                                   (FStar_UInt32.uint_to_t Prims.int_zero) in
                               let n2 = FStar_UInt32.uint_to_t Prims.int_zero in
                               let blast =
                                 FStar_Int_Cast.uint8_to_uint32 last2 in
                               FStar_UInt32.add blast
                                 (FStar_UInt32.mul n2
                                    (FStar_UInt32.uint_to_t
                                       (Prims.of_int (256)))) in
                             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                             FStar_UInt32.add blast
                               (FStar_UInt32.mul n1
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))) in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t (Prims.of_int (3)))))
              with
              | FStar_Pervasives_Native.Some (v, consumed) ->
                  if
                    Prims.op_Negation
                      ((FStar_UInt32.lt v min) || (FStar_UInt32.lt max v))
                  then FStar_Pervasives_Native.Some (v, consumed)
                  else FStar_Pervasives_Native.None
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v1, consumed) ->
            FStar_Pervasives_Native.Some (v1, consumed)
        | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t (Prims.of_int (4)))
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_zero)
                               (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                           let n =
                             let last1 =
                               FStar_Bytes.get first
                                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                             let first1 =
                               FStar_Bytes.slice first
                                 (FStar_UInt32.uint_to_t Prims.int_zero)
                                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                             let n1 =
                               let last2 =
                                 FStar_Bytes.get first1
                                   (FStar_UInt32.uint_to_t Prims.int_one) in
                               let first2 =
                                 FStar_Bytes.slice first1
                                   (FStar_UInt32.uint_to_t Prims.int_zero)
                                   (FStar_UInt32.uint_to_t Prims.int_one) in
                               let n2 =
                                 let last3 =
                                   FStar_Bytes.get first2
                                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                                 let first3 =
                                   FStar_Bytes.slice first2
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                                 let n3 =
                                   FStar_UInt32.uint_to_t Prims.int_zero in
                                 let blast =
                                   FStar_Int_Cast.uint8_to_uint32 last3 in
                                 FStar_UInt32.add blast
                                   (FStar_UInt32.mul n3
                                      (FStar_UInt32.uint_to_t
                                         (Prims.of_int (256)))) in
                               let blast =
                                 FStar_Int_Cast.uint8_to_uint32 last2 in
                               FStar_UInt32.add blast
                                 (FStar_UInt32.mul n2
                                    (FStar_UInt32.uint_to_t
                                       (Prims.of_int (256)))) in
                             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                             FStar_UInt32.add blast
                               (FStar_UInt32.mul n1
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))) in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t (Prims.of_int (4)))))
              with
              | FStar_Pervasives_Native.Some (v, consumed) ->
                  if
                    Prims.op_Negation
                      ((FStar_UInt32.lt v min) || (FStar_UInt32.lt max v))
                  then FStar_Pervasives_Native.Some (v, consumed)
                  else FStar_Pervasives_Native.None
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v1, consumed) ->
            FStar_Pervasives_Native.Some (v1, consumed)
        | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min32 ->
    fun max32 ->
      fun input ->
        if
          FStar_UInt32.lt max32 (FStar_UInt32.uint_to_t (Prims.of_int (256)))
        then parse32_bounded_int32_1 min32 max32 input
        else
          if
            FStar_UInt32.lt max32
              (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
          then parse32_bounded_int32_2 min32 max32 input
          else
            if
              FStar_UInt32.lt max32
                (FStar_UInt32.uint_to_t (Prims.parse_int "16777216"))
            then parse32_bounded_int32_3 min32 max32 input
            else parse32_bounded_int32_4 min32 max32 input
let (serialize32_bounded_int32' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min32 ->
    fun max32 ->
      fun sz32 ->
        fun input ->
          let x = input in
          match FStar_UInt32.v sz32 with
          | uu___ when uu___ = Prims.int_one ->
              FStar_Bytes.append FStar_Bytes.empty_bytes
                (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_Int_Cast.uint32_to_uint8 x))
          | uu___ when uu___ = (Prims.of_int (2)) ->
              FStar_Bytes.append
                (FStar_Bytes.append FStar_Bytes.empty_bytes
                   (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                      (FStar_Int_Cast.uint32_to_uint8
                         (FStar_UInt32.div x
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))))
                (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_Int_Cast.uint32_to_uint8 x))
          | uu___ when uu___ = (Prims.of_int (3)) ->
              FStar_Bytes.append
                (FStar_Bytes.append
                   (FStar_Bytes.append FStar_Bytes.empty_bytes
                      (FStar_Bytes.create
                         (FStar_UInt32.uint_to_t Prims.int_one)
                         (FStar_Int_Cast.uint32_to_uint8
                            (FStar_UInt32.div
                               (FStar_UInt32.div x
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256))))
                               (FStar_UInt32.uint_to_t (Prims.of_int (256)))))))
                   (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                      (FStar_Int_Cast.uint32_to_uint8
                         (FStar_UInt32.div x
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))))
                (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_Int_Cast.uint32_to_uint8 x))
          | uu___ when uu___ = (Prims.of_int (4)) ->
              FStar_Bytes.append
                (FStar_Bytes.append
                   (FStar_Bytes.append
                      (FStar_Bytes.append FStar_Bytes.empty_bytes
                         (FStar_Bytes.create
                            (FStar_UInt32.uint_to_t Prims.int_one)
                            (FStar_Int_Cast.uint32_to_uint8
                               (FStar_UInt32.div
                                  (FStar_UInt32.div
                                     (FStar_UInt32.div x
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (256))))
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))))))
                      (FStar_Bytes.create
                         (FStar_UInt32.uint_to_t Prims.int_one)
                         (FStar_Int_Cast.uint32_to_uint8
                            (FStar_UInt32.div
                               (FStar_UInt32.div x
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256))))
                               (FStar_UInt32.uint_to_t (Prims.of_int (256)))))))
                   (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                      (FStar_Int_Cast.uint32_to_uint8
                         (FStar_UInt32.div x
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))))))
                (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_Int_Cast.uint32_to_uint8 x))
let (serialize32_bounded_int32_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi = FStar_Bytes.empty_bytes in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_hi seq_lo
let (serialize32_bounded_int32_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi =
          let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
          let hi1 =
            FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi1 = FStar_Bytes.empty_bytes in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
          FStar_Bytes.append seq_hi1 seq_lo in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_hi seq_lo
let (serialize32_bounded_int32_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi =
          let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
          let hi1 =
            FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi1 =
            let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
            let hi2 =
              FStar_UInt32.div hi1
                (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
            let seq_hi2 = FStar_Bytes.empty_bytes in
            let seq_lo =
              FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
            FStar_Bytes.append seq_hi2 seq_lo in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
          FStar_Bytes.append seq_hi1 seq_lo in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_hi seq_lo
let (serialize32_bounded_int32_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi =
          let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
          let hi1 =
            FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi1 =
            let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
            let hi2 =
              FStar_UInt32.div hi1
                (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
            let seq_hi2 =
              let lo3 = FStar_Int_Cast.uint32_to_uint8 hi2 in
              let hi3 =
                FStar_UInt32.div hi2
                  (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
              let seq_hi3 = FStar_Bytes.empty_bytes in
              let seq_lo =
                FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo3 in
              FStar_Bytes.append seq_hi3 seq_lo in
            let seq_lo =
              FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
            FStar_Bytes.append seq_hi2 seq_lo in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
          FStar_Bytes.append seq_hi1 seq_lo in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_hi seq_lo
let (serialize32_bounded_int32 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min32 ->
    fun max32 ->
      fun input ->
        if
          FStar_UInt32.lt max32 (FStar_UInt32.uint_to_t (Prims.of_int (256)))
        then serialize32_bounded_int32_1 min32 max32 input
        else
          if
            FStar_UInt32.lt max32
              (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
          then serialize32_bounded_int32_2 min32 max32 input
          else
            if
              FStar_UInt32.lt max32
                (FStar_UInt32.uint_to_t (Prims.parse_int "16777216"))
            then serialize32_bounded_int32_3 min32 max32 input
            else serialize32_bounded_int32_4 min32 max32 input
let (parse32_bounded_int32_le' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        LowParse_SLow_Base.bytes32 ->
          (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min32 ->
    fun max32 ->
      fun sz32 ->
        fun input ->
          match match match FStar_UInt32.v sz32 with
                      | uu___ when uu___ = Prims.int_one ->
                          if
                            FStar_UInt32.lt (FStar_Bytes.len input)
                              (FStar_UInt32.uint_to_t Prims.int_one)
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              ((FStar_UInt32.add
                                  (FStar_Int_Cast.uint8_to_uint32
                                     (FStar_Bytes.get
                                        (FStar_Bytes.slice input
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_one))
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)))
                                  (FStar_UInt32.mul
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))),
                                (FStar_UInt32.uint_to_t Prims.int_one))
                      | uu___ when uu___ = (Prims.of_int (2)) ->
                          if
                            FStar_UInt32.lt (FStar_Bytes.len input)
                              (FStar_UInt32.uint_to_t (Prims.of_int (2)))
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              ((FStar_UInt32.add
                                  (FStar_Int_Cast.uint8_to_uint32
                                     (FStar_Bytes.get
                                        (FStar_Bytes.slice input
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (2))))
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)))
                                  (FStar_UInt32.mul
                                     (FStar_UInt32.add
                                        (FStar_Int_Cast.uint8_to_uint32
                                           (FStar_Bytes.get
                                              (FStar_Bytes.slice
                                                 (FStar_Bytes.slice input
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)
                                                    (FStar_UInt32.uint_to_t
                                                       (Prims.of_int (2))))
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_one)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (2))))
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero)))
                                        (FStar_UInt32.mul
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (256)))))
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))),
                                (FStar_UInt32.uint_to_t (Prims.of_int (2))))
                      | uu___ when uu___ = (Prims.of_int (3)) ->
                          if
                            FStar_UInt32.lt (FStar_Bytes.len input)
                              (FStar_UInt32.uint_to_t (Prims.of_int (3)))
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              ((FStar_UInt32.add
                                  (FStar_Int_Cast.uint8_to_uint32
                                     (FStar_Bytes.get
                                        (FStar_Bytes.slice input
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (3))))
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)))
                                  (FStar_UInt32.mul
                                     (FStar_UInt32.add
                                        (FStar_Int_Cast.uint8_to_uint32
                                           (FStar_Bytes.get
                                              (FStar_Bytes.slice
                                                 (FStar_Bytes.slice input
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)
                                                    (FStar_UInt32.uint_to_t
                                                       (Prims.of_int (3))))
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_one)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (3))))
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero)))
                                        (FStar_UInt32.mul
                                           (FStar_UInt32.add
                                              (FStar_Int_Cast.uint8_to_uint32
                                                 (FStar_Bytes.get
                                                    (FStar_Bytes.slice
                                                       (FStar_Bytes.slice
                                                          (FStar_Bytes.slice
                                                             input
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_zero)
                                                             (FStar_UInt32.uint_to_t
                                                                (Prims.of_int (3))))
                                                          (FStar_UInt32.uint_to_t
                                                             Prims.int_one)
                                                          (FStar_UInt32.uint_to_t
                                                             (Prims.of_int (3))))
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_one)
                                                       (FStar_UInt32.uint_to_t
                                                          (Prims.of_int (2))))
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)))
                                              (FStar_UInt32.mul
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (256)))))
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (256)))))
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))),
                                (FStar_UInt32.uint_to_t (Prims.of_int (3))))
                      | uu___ when uu___ = (Prims.of_int (4)) ->
                          if
                            FStar_UInt32.lt (FStar_Bytes.len input)
                              (FStar_UInt32.uint_to_t (Prims.of_int (4)))
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              ((FStar_UInt32.add
                                  (FStar_Int_Cast.uint8_to_uint32
                                     (FStar_Bytes.get
                                        (FStar_Bytes.slice input
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero)
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (4))))
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)))
                                  (FStar_UInt32.mul
                                     (FStar_UInt32.add
                                        (FStar_Int_Cast.uint8_to_uint32
                                           (FStar_Bytes.get
                                              (FStar_Bytes.slice
                                                 (FStar_Bytes.slice input
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)
                                                    (FStar_UInt32.uint_to_t
                                                       (Prims.of_int (4))))
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_one)
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (4))))
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero)))
                                        (FStar_UInt32.mul
                                           (FStar_UInt32.add
                                              (FStar_Int_Cast.uint8_to_uint32
                                                 (FStar_Bytes.get
                                                    (FStar_Bytes.slice
                                                       (FStar_Bytes.slice
                                                          (FStar_Bytes.slice
                                                             input
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_zero)
                                                             (FStar_UInt32.uint_to_t
                                                                (Prims.of_int (4))))
                                                          (FStar_UInt32.uint_to_t
                                                             Prims.int_one)
                                                          (FStar_UInt32.uint_to_t
                                                             (Prims.of_int (4))))
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_one)
                                                       (FStar_UInt32.uint_to_t
                                                          (Prims.of_int (3))))
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)))
                                              (FStar_UInt32.mul
                                                 (FStar_UInt32.add
                                                    (FStar_Int_Cast.uint8_to_uint32
                                                       (FStar_Bytes.get
                                                          (FStar_Bytes.slice
                                                             (FStar_Bytes.slice
                                                                (FStar_Bytes.slice
                                                                   (FStar_Bytes.slice
                                                                    input
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    (FStar_UInt32.uint_to_t
                                                                    (Prims.of_int (4))))
                                                                   (FStar_UInt32.uint_to_t
                                                                    Prims.int_one)
                                                                   (FStar_UInt32.uint_to_t
                                                                    (Prims.of_int (4))))
                                                                (FStar_UInt32.uint_to_t
                                                                   Prims.int_one)
                                                                (FStar_UInt32.uint_to_t
                                                                   (Prims.of_int (3))))
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_one)
                                                             (FStar_UInt32.uint_to_t
                                                                (Prims.of_int (2))))
                                                          (FStar_UInt32.uint_to_t
                                                             Prims.int_zero)))
                                                    (FStar_UInt32.mul
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_zero)
                                                       (FStar_UInt32.uint_to_t
                                                          (Prims.of_int (256)))))
                                                 (FStar_UInt32.uint_to_t
                                                    (Prims.of_int (256)))))
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (256)))))
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))),
                                (FStar_UInt32.uint_to_t (Prims.of_int (4))))
                with
                | FStar_Pervasives_Native.Some (v, consumed) ->
                    if
                      Prims.op_Negation
                        ((FStar_UInt32.lt v min32) ||
                           (FStar_UInt32.lt max32 v))
                    then FStar_Pervasives_Native.Some (v, consumed)
                    else FStar_Pervasives_Native.None
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some (v1, consumed)
          | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_le_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t Prims.int_one)
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t Prims.int_one) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_one)
                               (FStar_UInt32.uint_to_t Prims.int_one) in
                           let n = FStar_UInt32.uint_to_t Prims.int_zero in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t Prims.int_one)))
              with
              | FStar_Pervasives_Native.Some (v, consumed) ->
                  if
                    Prims.op_Negation
                      ((FStar_UInt32.lt v min) || (FStar_UInt32.lt max v))
                  then FStar_Pervasives_Native.Some (v, consumed)
                  else FStar_Pervasives_Native.None
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v1, consumed) ->
            FStar_Pervasives_Native.Some (v1, consumed)
        | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_le_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t (Prims.of_int (2)))
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_one)
                               (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                           let n =
                             let last1 =
                               FStar_Bytes.get first
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let first1 =
                               FStar_Bytes.slice first
                                 (FStar_UInt32.uint_to_t Prims.int_one)
                                 (FStar_UInt32.uint_to_t Prims.int_one) in
                             let n1 = FStar_UInt32.uint_to_t Prims.int_zero in
                             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                             FStar_UInt32.add blast
                               (FStar_UInt32.mul n1
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))) in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t (Prims.of_int (2)))))
              with
              | FStar_Pervasives_Native.Some (v, consumed) ->
                  if
                    Prims.op_Negation
                      ((FStar_UInt32.lt v min) || (FStar_UInt32.lt max v))
                  then FStar_Pervasives_Native.Some (v, consumed)
                  else FStar_Pervasives_Native.None
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v1, consumed) ->
            FStar_Pervasives_Native.Some (v1, consumed)
        | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_le_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t (Prims.of_int (3)))
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_one)
                               (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                           let n =
                             let last1 =
                               FStar_Bytes.get first
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let first1 =
                               FStar_Bytes.slice first
                                 (FStar_UInt32.uint_to_t Prims.int_one)
                                 (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                             let n1 =
                               let last2 =
                                 FStar_Bytes.get first1
                                   (FStar_UInt32.uint_to_t Prims.int_zero) in
                               let first2 =
                                 FStar_Bytes.slice first1
                                   (FStar_UInt32.uint_to_t Prims.int_one)
                                   (FStar_UInt32.uint_to_t Prims.int_one) in
                               let n2 = FStar_UInt32.uint_to_t Prims.int_zero in
                               let blast =
                                 FStar_Int_Cast.uint8_to_uint32 last2 in
                               FStar_UInt32.add blast
                                 (FStar_UInt32.mul n2
                                    (FStar_UInt32.uint_to_t
                                       (Prims.of_int (256)))) in
                             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                             FStar_UInt32.add blast
                               (FStar_UInt32.mul n1
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))) in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t (Prims.of_int (3)))))
              with
              | FStar_Pervasives_Native.Some (v, consumed) ->
                  if
                    Prims.op_Negation
                      ((FStar_UInt32.lt v min) || (FStar_UInt32.lt max v))
                  then FStar_Pervasives_Native.Some (v, consumed)
                  else FStar_Pervasives_Native.None
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v1, consumed) ->
            FStar_Pervasives_Native.Some (v1, consumed)
        | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_le_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t (Prims.of_int (4)))
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_one)
                               (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                           let n =
                             let last1 =
                               FStar_Bytes.get first
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let first1 =
                               FStar_Bytes.slice first
                                 (FStar_UInt32.uint_to_t Prims.int_one)
                                 (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                             let n1 =
                               let last2 =
                                 FStar_Bytes.get first1
                                   (FStar_UInt32.uint_to_t Prims.int_zero) in
                               let first2 =
                                 FStar_Bytes.slice first1
                                   (FStar_UInt32.uint_to_t Prims.int_one)
                                   (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                               let n2 =
                                 let last3 =
                                   FStar_Bytes.get first2
                                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                                 let first3 =
                                   FStar_Bytes.slice first2
                                     (FStar_UInt32.uint_to_t Prims.int_one)
                                     (FStar_UInt32.uint_to_t Prims.int_one) in
                                 let n3 =
                                   FStar_UInt32.uint_to_t Prims.int_zero in
                                 let blast =
                                   FStar_Int_Cast.uint8_to_uint32 last3 in
                                 FStar_UInt32.add blast
                                   (FStar_UInt32.mul n3
                                      (FStar_UInt32.uint_to_t
                                         (Prims.of_int (256)))) in
                               let blast =
                                 FStar_Int_Cast.uint8_to_uint32 last2 in
                               FStar_UInt32.add blast
                                 (FStar_UInt32.mul n2
                                    (FStar_UInt32.uint_to_t
                                       (Prims.of_int (256)))) in
                             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                             FStar_UInt32.add blast
                               (FStar_UInt32.mul n1
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))) in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t (Prims.of_int (4)))))
              with
              | FStar_Pervasives_Native.Some (v, consumed) ->
                  if
                    Prims.op_Negation
                      ((FStar_UInt32.lt v min) || (FStar_UInt32.lt max v))
                  then FStar_Pervasives_Native.Some (v, consumed)
                  else FStar_Pervasives_Native.None
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v1, consumed) ->
            FStar_Pervasives_Native.Some (v1, consumed)
        | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_int32_le :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min32 ->
    fun max32 ->
      fun input ->
        if
          FStar_UInt32.lt max32 (FStar_UInt32.uint_to_t (Prims.of_int (256)))
        then parse32_bounded_int32_le_1 min32 max32 input
        else
          if
            FStar_UInt32.lt max32
              (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
          then parse32_bounded_int32_le_2 min32 max32 input
          else
            if
              FStar_UInt32.lt max32
                (FStar_UInt32.uint_to_t (Prims.parse_int "16777216"))
            then parse32_bounded_int32_le_3 min32 max32 input
            else parse32_bounded_int32_le_4 min32 max32 input
let (serialize32_bounded_int32_le' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min32 ->
    fun max32 ->
      fun sz32 ->
        fun input ->
          let x = input in
          match FStar_UInt32.v sz32 with
          | uu___ when uu___ = Prims.int_one ->
              FStar_Bytes.append
                (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_Int_Cast.uint32_to_uint8 x))
                FStar_Bytes.empty_bytes
          | uu___ when uu___ = (Prims.of_int (2)) ->
              FStar_Bytes.append
                (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_Int_Cast.uint32_to_uint8 x))
                (FStar_Bytes.append
                   (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                      (FStar_Int_Cast.uint32_to_uint8
                         (FStar_UInt32.div x
                            (FStar_UInt32.uint_to_t (Prims.of_int (256))))))
                   FStar_Bytes.empty_bytes)
          | uu___ when uu___ = (Prims.of_int (3)) ->
              FStar_Bytes.append
                (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_Int_Cast.uint32_to_uint8 x))
                (FStar_Bytes.append
                   (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                      (FStar_Int_Cast.uint32_to_uint8
                         (FStar_UInt32.div x
                            (FStar_UInt32.uint_to_t (Prims.of_int (256))))))
                   (FStar_Bytes.append
                      (FStar_Bytes.create
                         (FStar_UInt32.uint_to_t Prims.int_one)
                         (FStar_Int_Cast.uint32_to_uint8
                            (FStar_UInt32.div
                               (FStar_UInt32.div x
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256))))
                               (FStar_UInt32.uint_to_t (Prims.of_int (256))))))
                      FStar_Bytes.empty_bytes))
          | uu___ when uu___ = (Prims.of_int (4)) ->
              FStar_Bytes.append
                (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                   (FStar_Int_Cast.uint32_to_uint8 x))
                (FStar_Bytes.append
                   (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                      (FStar_Int_Cast.uint32_to_uint8
                         (FStar_UInt32.div x
                            (FStar_UInt32.uint_to_t (Prims.of_int (256))))))
                   (FStar_Bytes.append
                      (FStar_Bytes.create
                         (FStar_UInt32.uint_to_t Prims.int_one)
                         (FStar_Int_Cast.uint32_to_uint8
                            (FStar_UInt32.div
                               (FStar_UInt32.div x
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256))))
                               (FStar_UInt32.uint_to_t (Prims.of_int (256))))))
                      (FStar_Bytes.append
                         (FStar_Bytes.create
                            (FStar_UInt32.uint_to_t Prims.int_one)
                            (FStar_Int_Cast.uint32_to_uint8
                               (FStar_UInt32.div
                                  (FStar_UInt32.div
                                     (FStar_UInt32.div x
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (256))))
                                     (FStar_UInt32.uint_to_t
                                        (Prims.of_int (256))))
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256))))))
                         FStar_Bytes.empty_bytes)))
let (serialize32_bounded_int32_le_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi = FStar_Bytes.empty_bytes in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_lo seq_hi
let (serialize32_bounded_int32_le_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi =
          let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
          let hi1 =
            FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi1 = FStar_Bytes.empty_bytes in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
          FStar_Bytes.append seq_lo seq_hi1 in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_lo seq_hi
let (serialize32_bounded_int32_le_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi =
          let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
          let hi1 =
            FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi1 =
            let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
            let hi2 =
              FStar_UInt32.div hi1
                (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
            let seq_hi2 = FStar_Bytes.empty_bytes in
            let seq_lo =
              FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
            FStar_Bytes.append seq_lo seq_hi2 in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
          FStar_Bytes.append seq_lo seq_hi1 in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_lo seq_hi
let (serialize32_bounded_int32_le_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi =
          let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
          let hi1 =
            FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi1 =
            let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
            let hi2 =
              FStar_UInt32.div hi1
                (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
            let seq_hi2 =
              let lo3 = FStar_Int_Cast.uint32_to_uint8 hi2 in
              let hi3 =
                FStar_UInt32.div hi2
                  (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
              let seq_hi3 = FStar_Bytes.empty_bytes in
              let seq_lo =
                FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo3 in
              FStar_Bytes.append seq_lo seq_hi3 in
            let seq_lo =
              FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
            FStar_Bytes.append seq_lo seq_hi2 in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
          FStar_Bytes.append seq_lo seq_hi1 in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_lo seq_hi
let (serialize32_bounded_int32_le :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min32 ->
    fun max32 ->
      fun input ->
        if
          FStar_UInt32.lt max32 (FStar_UInt32.uint_to_t (Prims.of_int (256)))
        then serialize32_bounded_int32_le_1 min32 max32 input
        else
          if
            FStar_UInt32.lt max32
              (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
          then serialize32_bounded_int32_le_2 min32 max32 input
          else
            if
              FStar_UInt32.lt max32
                (FStar_UInt32.uint_to_t (Prims.parse_int "16777216"))
            then serialize32_bounded_int32_le_3 min32 max32 input
            else serialize32_bounded_int32_le_4 min32 max32 input
let (parse32_bounded_int32_le_fixed_size :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min32 ->
    fun max32 ->
      fun input ->
        match match if
                      FStar_UInt32.lt (FStar_Bytes.len input)
                        (FStar_UInt32.uint_to_t (Prims.of_int (4)))
                    then FStar_Pervasives_Native.None
                    else
                      (let s' =
                         FStar_Bytes.slice input
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                       FStar_Pervasives_Native.Some
                         ((let last =
                             FStar_Bytes.get s'
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                           let first =
                             FStar_Bytes.slice s'
                               (FStar_UInt32.uint_to_t Prims.int_one)
                               (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                           let n =
                             let last1 =
                               FStar_Bytes.get first
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let first1 =
                               FStar_Bytes.slice first
                                 (FStar_UInt32.uint_to_t Prims.int_one)
                                 (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                             let n1 =
                               let last2 =
                                 FStar_Bytes.get first1
                                   (FStar_UInt32.uint_to_t Prims.int_zero) in
                               let first2 =
                                 FStar_Bytes.slice first1
                                   (FStar_UInt32.uint_to_t Prims.int_one)
                                   (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                               let n2 =
                                 let last3 =
                                   FStar_Bytes.get first2
                                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                                 let first3 =
                                   FStar_Bytes.slice first2
                                     (FStar_UInt32.uint_to_t Prims.int_one)
                                     (FStar_UInt32.uint_to_t Prims.int_one) in
                                 let n3 =
                                   FStar_UInt32.uint_to_t Prims.int_zero in
                                 let blast =
                                   FStar_Int_Cast.uint8_to_uint32 last3 in
                                 FStar_UInt32.add blast
                                   (FStar_UInt32.mul n3
                                      (FStar_UInt32.uint_to_t
                                         (Prims.of_int (256)))) in
                               let blast =
                                 FStar_Int_Cast.uint8_to_uint32 last2 in
                               FStar_UInt32.add blast
                                 (FStar_UInt32.mul n2
                                    (FStar_UInt32.uint_to_t
                                       (Prims.of_int (256)))) in
                             let blast = FStar_Int_Cast.uint8_to_uint32 last1 in
                             FStar_UInt32.add blast
                               (FStar_UInt32.mul n1
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))) in
                           let blast = FStar_Int_Cast.uint8_to_uint32 last in
                           FStar_UInt32.add blast
                             (FStar_UInt32.mul n
                                (FStar_UInt32.uint_to_t (Prims.of_int (256))))),
                           (FStar_UInt32.uint_to_t (Prims.of_int (4)))))
              with
              | FStar_Pervasives_Native.Some (v1, consumed) ->
                  FStar_Pervasives_Native.Some (v1, consumed)
              | uu___ -> FStar_Pervasives_Native.None
        with
        | FStar_Pervasives_Native.Some (v, consumed) ->
            if
              Prims.op_Negation
                ((FStar_UInt32.lt v min32) || (FStar_UInt32.lt max32 v))
            then FStar_Pervasives_Native.Some (v, consumed)
            else FStar_Pervasives_Native.None
        | uu___ -> FStar_Pervasives_Native.None
let (serialize32_bounded_int32_le_fixed_size :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun min32 ->
    fun max32 ->
      fun input ->
        let x = input in
        let lo = FStar_Int_Cast.uint32_to_uint8 x in
        let hi =
          FStar_UInt32.div x (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
        let seq_hi =
          let lo1 = FStar_Int_Cast.uint32_to_uint8 hi in
          let hi1 =
            FStar_UInt32.div hi (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
          let seq_hi1 =
            let lo2 = FStar_Int_Cast.uint32_to_uint8 hi1 in
            let hi2 =
              FStar_UInt32.div hi1
                (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
            let seq_hi2 =
              let lo3 = FStar_Int_Cast.uint32_to_uint8 hi2 in
              let hi3 =
                FStar_UInt32.div hi2
                  (FStar_UInt32.uint_to_t (Prims.of_int (256))) in
              let seq_hi3 = FStar_Bytes.empty_bytes in
              let seq_lo =
                FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo3 in
              FStar_Bytes.append seq_lo seq_hi3 in
            let seq_lo =
              FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo2 in
            FStar_Bytes.append seq_lo seq_hi2 in
          let seq_lo =
            FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
          FStar_Bytes.append seq_lo seq_hi1 in
        let seq_lo =
          FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
        FStar_Bytes.append seq_lo seq_hi