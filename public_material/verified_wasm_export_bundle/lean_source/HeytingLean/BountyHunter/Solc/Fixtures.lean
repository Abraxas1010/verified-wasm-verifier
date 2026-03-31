import Lean
import Lean.Data.Json
import HeytingLean.BountyHunter.Solc.ExtractIR

/-!
# HeytingLean.BountyHunter.Solc.Fixtures

A tiny, pinned fixture for auditing the one-way solc → YulTextMini → AlgebraIR pipeline.

Source was compiled with `solc --standard-json` and `outputSelection: ["ir"]`.
Solc version observed at capture time: 0.8.33 (linux-arm64 static).
-/

namespace HeytingLean.BountyHunter.Solc.Fixtures

open Lean
open Lean.Json

def sourceUnit : String := "BountyHunterTarget.sol"
def contractName : String := "BountyHunterTarget"
def field : String := "ir"
def desiredFunc : String := "withdraw"
def slot : Nat := 0

def selector : HeytingLean.BountyHunter.Solc.Selector :=
  { sourceUnit := sourceUnit, contractName := contractName, field := field }

def ir : String := r#"
/// @use-src 0:"BountyHunterTarget.sol"
object "BountyHunterTarget_30" {
    code {
        /// @src 0:65:292  "contract BountyHunterTarget {..."
        mstore(64, memoryguard(128))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        constructor_BountyHunterTarget_30()

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("BountyHunterTarget_30_deployed"), datasize("BountyHunterTarget_30_deployed"))

        return(_1, datasize("BountyHunterTarget_30_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        function shift_left_0(value) -> newValue {
            newValue :=

            shl(0, value)

        }

        function update_byte_slice_32_shift_0(value, toInsert) -> result {
            let mask := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
            toInsert := shift_left_0(toInsert)
            value := and(value, not(mask))
            result := or(value, and(toInsert, mask))
        }

        function cleanup_t_rational_1_by_1(value) -> cleaned {
            cleaned := value
        }

        function cleanup_t_uint256(value) -> cleaned {
            cleaned := value
        }

        function identity(value) -> ret {
            ret := value
        }

        function convert_t_rational_1_by_1_to_t_uint256(value) -> converted {
            converted := cleanup_t_uint256(identity(cleanup_t_rational_1_by_1(value)))
        }

        function prepare_store_t_uint256(value) -> ret {
            ret := value
        }

        function update_storage_value_offset_0_t_rational_1_by_1_to_t_uint256(slot, value_0) {
            let convertedValue_0 := convert_t_rational_1_by_1_to_t_uint256(value_0)
            sstore(slot, update_byte_slice_32_shift_0(sload(slot), prepare_store_t_uint256(convertedValue_0)))
        }

        /// @src 0:65:292  "contract BountyHunterTarget {..."
        function constructor_BountyHunterTarget_30() {

            /// @src 0:65:292  "contract BountyHunterTarget {..."

            /// @src 0:118:119  "1"
            let expr_3 := 0x01
            update_storage_value_offset_0_t_rational_1_by_1_to_t_uint256(0x00, expr_3)

        }
        /// @src 0:65:292  "contract BountyHunterTarget {..."

    }
    /// @use-src 0:"BountyHunterTarget.sol"
    object "BountyHunterTarget_30_deployed" {
        code {
            /// @src 0:65:292  "contract BountyHunterTarget {..."
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x0c55699c
                {
                    // x()

                    external_fun_x_4()
                }

                case 0x3ccfd60b
                {
                    // withdraw()

                    external_fun_withdraw_25()
                }

                default {}
            }
            if iszero(calldatasize()) { fun__29() stop() }
            revert_error_d228b4ceac16d8e91d6dc7ca8d4a5394f524b2e550555324088cb23b86b87b98()

            function shift_right_224_unsigned(value) -> newValue {
                newValue :=

                shr(224, value)

            }

            function allocate_unbounded() -> memPtr {
                memPtr := mload(64)
            }

            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
                revert(0, 0)
            }

            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {
                revert(0, 0)
            }

            function abi_decode_tuple_(headStart, dataEnd)   {
                if slt(sub(dataEnd, headStart), 0) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

            }

            function shift_right_unsigned_dynamic(bits, value) -> newValue {
                newValue :=

                shr(bits, value)

            }

            function cleanup_from_storage_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function extract_from_storage_value_dynamict_uint256(slot_value, offset) -> value {
                value := cleanup_from_storage_t_uint256(shift_right_unsigned_dynamic(mul(offset, 8), slot_value))
            }

            function read_from_storage_split_dynamic_t_uint256(slot, offset) -> value {
                value := extract_from_storage_value_dynamict_uint256(sload(slot), offset)

            }

            /// @ast-id 4
            /// @src 0:99:119  "uint256 public x = 1"
            function getter_fun_x_4() -> ret {

                let slot := 0
                let offset := 0

                ret := read_from_storage_split_dynamic_t_uint256(slot, offset)

            }
            /// @src 0:65:292  "contract BountyHunterTarget {..."

            function cleanup_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function abi_encode_t_uint256_to_t_uint256_fromStack(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_x_4() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                let ret_0 :=  getter_fun_x_4()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function abi_encode_tuple__to__fromStack(headStart ) -> tail {
                tail := add(headStart, 0)

            }

            function external_fun_withdraw_25() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                fun_withdraw_25()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple__to__fromStack(memPos  )
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_d228b4ceac16d8e91d6dc7ca8d4a5394f524b2e550555324088cb23b86b87b98() {
                revert(0, 0)
            }

            function array_storeLengthForEncoding_t_bytes_memory_ptr_nonPadded_inplace_fromStack(pos, length) -> updated_pos {
                updated_pos := pos
            }

            function store_literal_in_memory_c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470(memPtr) {

            }

            function abi_encode_t_stringliteral_c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470_to_t_bytes_memory_ptr_nonPadded_inplace_fromStack(pos) -> end {
                pos := array_storeLengthForEncoding_t_bytes_memory_ptr_nonPadded_inplace_fromStack(pos, 0)
                store_literal_in_memory_c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470(pos)
                end := add(pos, 0)
            }

            function abi_encode_tuple_packed_t_stringliteral_c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470__to_t_bytes_memory_ptr__nonPadded_inplace_fromStack(pos ) -> end {

                pos := abi_encode_t_stringliteral_c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470_to_t_bytes_memory_ptr_nonPadded_inplace_fromStack( pos)

                end := pos
            }

            function round_up_to_mul_of_32(value) -> result {
                result := and(add(value, 31), not(31))
            }

            function panic_error_0x41() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x41)
                revert(0, 0x24)
            }

            function finalize_allocation(memPtr, size) {
                let newFreePtr := add(memPtr, round_up_to_mul_of_32(size))
                // protect against overflow
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }

            function allocate_memory(size) -> memPtr {
                memPtr := allocate_unbounded()
                finalize_allocation(memPtr, size)
            }

            function array_allocation_size_t_bytes_memory_ptr(length) -> size {
                // Make sure we can allocate memory without overflow
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }

                size := round_up_to_mul_of_32(length)

                // add length slot
                size := add(size, 0x20)

            }

            function allocate_memory_array_t_bytes_memory_ptr(length) -> memPtr {
                let allocSize := array_allocation_size_t_bytes_memory_ptr(length)
                memPtr := allocate_memory(allocSize)

                mstore(memPtr, length)

            }

            function zero_value_for_split_t_bytes_memory_ptr() -> ret {
                ret := 96
            }

            function extract_returndata() -> data {

                switch returndatasize()
                case 0 {
                    data := zero_value_for_split_t_bytes_memory_ptr()
                }
                default {
                    data := allocate_memory_array_t_bytes_memory_ptr(returndatasize())
                    returndatacopy(add(data, 0x20), 0, returndatasize())
                }

            }

            function array_storeLengthForEncoding_t_string_memory_ptr_fromStack(pos, length) -> updated_pos {
                mstore(pos, length)
                updated_pos := add(pos, 0x20)
            }

            function store_literal_in_memory_a04f7977a7361020e07a160885cb05178aa6d9ff17ec37e942914b4316b9352a(memPtr) {

                mstore(add(memPtr, 0), "call failed")

            }

            function abi_encode_t_stringliteral_a04f7977a7361020e07a160885cb05178aa6d9ff17ec37e942914b4316b9352a_to_t_string_memory_ptr_fromStack(pos) -> end {
                pos := array_storeLengthForEncoding_t_string_memory_ptr_fromStack(pos, 11)
                store_literal_in_memory_a04f7977a7361020e07a160885cb05178aa6d9ff17ec37e942914b4316b9352a(pos)
                end := add(pos, 32)
            }

            function abi_encode_tuple_t_stringliteral_a04f7977a7361020e07a160885cb05178aa6d9ff17ec37e942914b4316b9352a__to_t_string_memory_ptr__fromStack(headStart ) -> tail {
                tail := add(headStart, 32)

                mstore(add(headStart, 0), sub(tail, headStart))
                tail := abi_encode_t_stringliteral_a04f7977a7361020e07a160885cb05178aa6d9ff17ec37e942914b4316b9352a_to_t_string_memory_ptr_fromStack( tail)

            }

            function require_helper_t_stringliteral_a04f7977a7361020e07a160885cb05178aa6d9ff17ec37e942914b4316b9352a(condition ) {
                if iszero(condition)
                {

                    let memPtr := allocate_unbounded()

                    mstore(memPtr, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    let end := abi_encode_tuple_t_stringliteral_a04f7977a7361020e07a160885cb05178aa6d9ff17ec37e942914b4316b9352a__to_t_string_memory_ptr__fromStack(add(memPtr, 4) )
                    revert(memPtr, sub(end, memPtr))
                }
            }

            function cleanup_t_rational_0_by_1(value) -> cleaned {
                cleaned := value
            }

            function identity(value) -> ret {
                ret := value
            }

            function convert_t_rational_0_by_1_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_rational_0_by_1(value)))
            }

            function shift_left_0(value) -> newValue {
                newValue :=

                shl(0, value)

            }

            function update_byte_slice_32_shift_0(value, toInsert) -> result {
                let mask := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                toInsert := shift_left_0(toInsert)
                value := and(value, not(mask))
                result := or(value, and(toInsert, mask))
            }

            function convert_t_uint256_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_uint256(value)))
            }

            function prepare_store_t_uint256(value) -> ret {
                ret := value
            }

            function update_storage_value_offset_0_t_uint256_to_t_uint256(slot, value_0) {
                let convertedValue_0 := convert_t_uint256_to_t_uint256(value_0)
                sstore(slot, update_byte_slice_32_shift_0(sload(slot), prepare_store_t_uint256(convertedValue_0)))
            }

            /// @ast-id 25
            /// @src 0:126:255  "function withdraw() external {..."
            function fun_withdraw_25() {

                /// @src 0:178:188  "msg.sender"
                let expr_10 := caller()
                /// @src 0:178:193  "msg.sender.call"
                let expr_11_address := expr_10
                /// @src 0:178:197  "msg.sender.call(\"\")"

                let _1 := allocate_unbounded()
                let _2 := sub(abi_encode_tuple_packed_t_stringliteral_c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470__to_t_bytes_memory_ptr__nonPadded_inplace_fromStack(_1  ), _1)

                let expr_13_component_1 := call(gas(), expr_11_address,  0,  _1, _2, 0, 0)

                let expr_13_component_2_mpos := extract_returndata()
                /// @src 0:165:197  "(bool ok,) = msg.sender.call(\"\")"
                let var_ok_8 := expr_13_component_1
                /// @src 0:215:217  "ok"
                let _3 := var_ok_8
                let expr_16 := _3
                /// @src 0:207:233  "require(ok, \"call failed\")"
                require_helper_t_stringliteral_a04f7977a7361020e07a160885cb05178aa6d9ff17ec37e942914b4316b9352a(expr_16)
                /// @src 0:247:248  "0"
                let expr_21 := 0x00
                /// @src 0:243:248  "x = 0"
                let _4 := convert_t_rational_0_by_1_to_t_uint256(expr_21)
                update_storage_value_offset_0_t_uint256_to_t_uint256(0x00, _4)
                let expr_22 := _4

            }
            /// @src 0:65:292  "contract BountyHunterTarget {..."

            /// @ast-id 29
            /// @src 0:261:290  "receive() external payable {}"
            function fun__29() {

            }
            /// @src 0:65:292  "contract BountyHunterTarget {..."

        }

        data ".metadata" hex"a26469706673582212201ea2cd4e8c0c9e54548dde8e15d4a62ca6de3adedf42b0d48dab1f0182b6741264736f6c63430008210033"
    }

}


"#

def solcOutJson : Lean.Json :=
  Json.mkObj
    [ ("contracts",
        Json.mkObj
          [ (sourceUnit,
              Json.mkObj
                [ (contractName, Json.mkObj [ (field, Json.str ir) ]) ]) ]) ]

end HeytingLean.BountyHunter.Solc.Fixtures
