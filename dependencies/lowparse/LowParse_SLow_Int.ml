open Prims
let (parse32_u8 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt8.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
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
         ((let r = FStar_Bytes.get s' (FStar_UInt32.uint_to_t Prims.int_zero) in
           r), (FStar_UInt32.uint_to_t Prims.int_one)))
let (serialize32_u8 : FStar_UInt8.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let b = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) input in
    b
let (parse32_u16 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt16.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
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
             let n1 = FStar_UInt16.uint_to_t Prims.int_zero in
             let blast = FStar_Int_Cast.uint8_to_uint16 last1 in
             FStar_UInt16.add blast
               (FStar_UInt16.mul n1
                  (FStar_UInt16.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint16 last in
           FStar_UInt16.add blast
             (FStar_UInt16.mul n
                (FStar_UInt16.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t (Prims.of_int (2)))))
let (serialize32_u16 : FStar_UInt16.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let lo = FStar_Int_Cast.uint16_to_uint8 input in
    let hi =
      FStar_UInt16.div input (FStar_UInt16.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint16_to_uint8 hi in
      let hi1 =
        FStar_UInt16.div hi (FStar_UInt16.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 = FStar_Bytes.empty_bytes in
      let seq_lo =
        FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo1 in
      FStar_Bytes.append seq_hi1 seq_lo in
    let seq_lo = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo in
    FStar_Bytes.append seq_hi seq_lo
let (parse32_u32 :
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
let (serialize32_u32 : FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
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
let (parse32_u64 :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt64.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (8)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
       FStar_Pervasives_Native.Some
         ((let last =
             FStar_Bytes.get s' (FStar_UInt32.uint_to_t (Prims.of_int (7))) in
           let first =
             FStar_Bytes.slice s' (FStar_UInt32.uint_to_t Prims.int_zero)
               (FStar_UInt32.uint_to_t (Prims.of_int (7))) in
           let n =
             let last1 =
               FStar_Bytes.get first
                 (FStar_UInt32.uint_to_t (Prims.of_int (6))) in
             let first1 =
               FStar_Bytes.slice first
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t (Prims.of_int (6))) in
             let n1 =
               let last2 =
                 FStar_Bytes.get first1
                   (FStar_UInt32.uint_to_t (Prims.of_int (5))) in
               let first2 =
                 FStar_Bytes.slice first1
                   (FStar_UInt32.uint_to_t Prims.int_zero)
                   (FStar_UInt32.uint_to_t (Prims.of_int (5))) in
               let n2 =
                 let last3 =
                   FStar_Bytes.get first2
                     (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                 let first3 =
                   FStar_Bytes.slice first2
                     (FStar_UInt32.uint_to_t Prims.int_zero)
                     (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                 let n3 =
                   let last4 =
                     FStar_Bytes.get first3
                       (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                   let first4 =
                     FStar_Bytes.slice first3
                       (FStar_UInt32.uint_to_t Prims.int_zero)
                       (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
                   let n4 =
                     let last5 =
                       FStar_Bytes.get first4
                         (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                     let first5 =
                       FStar_Bytes.slice first4
                         (FStar_UInt32.uint_to_t Prims.int_zero)
                         (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                     let n5 =
                       let last6 =
                         FStar_Bytes.get first5
                           (FStar_UInt32.uint_to_t Prims.int_one) in
                       let first6 =
                         FStar_Bytes.slice first5
                           (FStar_UInt32.uint_to_t Prims.int_zero)
                           (FStar_UInt32.uint_to_t Prims.int_one) in
                       let n6 =
                         let last7 =
                           FStar_Bytes.get first6
                             (FStar_UInt32.uint_to_t Prims.int_zero) in
                         let first7 =
                           FStar_Bytes.slice first6
                             (FStar_UInt32.uint_to_t Prims.int_zero)
                             (FStar_UInt32.uint_to_t Prims.int_zero) in
                         let n7 = FStar_UInt64.uint_to_t Prims.int_zero in
                         let blast = FStar_Int_Cast.uint8_to_uint64 last7 in
                         FStar_UInt64.add blast
                           (FStar_UInt64.mul n7
                              (FStar_UInt64.uint_to_t (Prims.of_int (256)))) in
                       let blast = FStar_Int_Cast.uint8_to_uint64 last6 in
                       FStar_UInt64.add blast
                         (FStar_UInt64.mul n6
                            (FStar_UInt64.uint_to_t (Prims.of_int (256)))) in
                     let blast = FStar_Int_Cast.uint8_to_uint64 last5 in
                     FStar_UInt64.add blast
                       (FStar_UInt64.mul n5
                          (FStar_UInt64.uint_to_t (Prims.of_int (256)))) in
                   let blast = FStar_Int_Cast.uint8_to_uint64 last4 in
                   FStar_UInt64.add blast
                     (FStar_UInt64.mul n4
                        (FStar_UInt64.uint_to_t (Prims.of_int (256)))) in
                 let blast = FStar_Int_Cast.uint8_to_uint64 last3 in
                 FStar_UInt64.add blast
                   (FStar_UInt64.mul n3
                      (FStar_UInt64.uint_to_t (Prims.of_int (256)))) in
               let blast = FStar_Int_Cast.uint8_to_uint64 last2 in
               FStar_UInt64.add blast
                 (FStar_UInt64.mul n2
                    (FStar_UInt64.uint_to_t (Prims.of_int (256)))) in
             let blast = FStar_Int_Cast.uint8_to_uint64 last1 in
             FStar_UInt64.add blast
               (FStar_UInt64.mul n1
                  (FStar_UInt64.uint_to_t (Prims.of_int (256)))) in
           let blast = FStar_Int_Cast.uint8_to_uint64 last in
           FStar_UInt64.add blast
             (FStar_UInt64.mul n
                (FStar_UInt64.uint_to_t (Prims.of_int (256))))),
           (FStar_UInt32.uint_to_t (Prims.of_int (8)))))
let (serialize32_u64 : FStar_UInt64.t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let lo = FStar_Int_Cast.uint64_to_uint8 input in
    let hi =
      FStar_UInt64.div input (FStar_UInt64.uint_to_t (Prims.of_int (256))) in
    let seq_hi =
      let lo1 = FStar_Int_Cast.uint64_to_uint8 hi in
      let hi1 =
        FStar_UInt64.div hi (FStar_UInt64.uint_to_t (Prims.of_int (256))) in
      let seq_hi1 =
        let lo2 = FStar_Int_Cast.uint64_to_uint8 hi1 in
        let hi2 =
          FStar_UInt64.div hi1 (FStar_UInt64.uint_to_t (Prims.of_int (256))) in
        let seq_hi2 =
          let lo3 = FStar_Int_Cast.uint64_to_uint8 hi2 in
          let hi3 =
            FStar_UInt64.div hi2
              (FStar_UInt64.uint_to_t (Prims.of_int (256))) in
          let seq_hi3 =
            let lo4 = FStar_Int_Cast.uint64_to_uint8 hi3 in
            let hi4 =
              FStar_UInt64.div hi3
                (FStar_UInt64.uint_to_t (Prims.of_int (256))) in
            let seq_hi4 =
              let lo5 = FStar_Int_Cast.uint64_to_uint8 hi4 in
              let hi5 =
                FStar_UInt64.div hi4
                  (FStar_UInt64.uint_to_t (Prims.of_int (256))) in
              let seq_hi5 =
                let lo6 = FStar_Int_Cast.uint64_to_uint8 hi5 in
                let hi6 =
                  FStar_UInt64.div hi5
                    (FStar_UInt64.uint_to_t (Prims.of_int (256))) in
                let seq_hi6 =
                  let lo7 = FStar_Int_Cast.uint64_to_uint8 hi6 in
                  let hi7 =
                    FStar_UInt64.div hi6
                      (FStar_UInt64.uint_to_t (Prims.of_int (256))) in
                  let seq_hi7 = FStar_Bytes.empty_bytes in
                  let seq_lo =
                    FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                      lo7 in
                  FStar_Bytes.append seq_hi7 seq_lo in
                let seq_lo =
                  FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                    lo6 in
                FStar_Bytes.append seq_hi6 seq_lo in
              let seq_lo =
                FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo5 in
              FStar_Bytes.append seq_hi5 seq_lo in
            let seq_lo =
              FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) lo4 in
            FStar_Bytes.append seq_hi4 seq_lo in
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
let (size32_u8 : FStar_UInt8.t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one
let (size32_u16 : FStar_UInt16.t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (2))
let (size32_u32 : FStar_UInt32.t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))
let (size32_u64 : FStar_UInt64.t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (8))