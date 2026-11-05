cfg_if::cfg_if! {
    if #[cfg(target_os = "zkvm")] {
        mod zkm;
        use zkm::poseidon2_sponge;
    } else {
        mod permute;
        use permute::poseidon2_sponge;
    }
}

const WIDTH: usize = 16; // Number of field elements in the Poseidon2 state
const RATE: usize = 8; // Number of field elements processed per round
const FIELD_SIZE: usize = 3; // Number of bytes can be safely converted to field element

const STACK_BUFFER_SIZE: usize = 192; // Size of the stack buffer for small inputs

#[inline(always)]
fn poseidon2_core<const OUTPUT_SIZE: usize>(input: &[u8]) -> [u8; OUTPUT_SIZE] {
    let mut state = [0u32; WIDTH];
    let input_len = input.len();
    let padded_len = (input_len + FIELD_SIZE) / FIELD_SIZE * FIELD_SIZE;

    if padded_len <= STACK_BUFFER_SIZE {
        let mut padded_buf = [0u8; STACK_BUFFER_SIZE];
        poseidon2_small_input(input, &mut padded_buf, &mut state);
    } else {
        poseidon2_large_input(input, &mut state);
    }

    let mut result = [0u8; OUTPUT_SIZE];
    unsafe {
        std::ptr::copy_nonoverlapping(
            state.as_ptr() as *const u8,
            result.as_mut_ptr(),
            OUTPUT_SIZE,
        );
    }
    result
}

#[inline(always)]
pub fn poseidon2(input: &[u8]) -> [u8; 32] {
    poseidon2_core::<32>(input)
}

#[inline(always)]
pub fn poseidon2_128(input: &[u8]) -> [u8; 16] {
    poseidon2_core::<16>(input)
}

#[inline(always)]
fn poseidon2_small_input(input: &[u8], padded_buf: &mut [u8], state: &mut [u32; WIDTH]) {
    let input_len = input.len();
    let padded_len = (input_len + FIELD_SIZE) / FIELD_SIZE * FIELD_SIZE;

    unsafe {
        std::ptr::copy_nonoverlapping(input.as_ptr(), padded_buf.as_mut_ptr(), input_len);
        std::ptr::write_bytes(
            padded_buf.as_mut_ptr().add(input_len),
            0,
            padded_len - input_len,
        );
    }

    apply_padding(padded_buf, input_len, padded_len);
    poseidon2_sponge(&padded_buf[..padded_len], state);
}

#[inline]
fn poseidon2_large_input(input: &[u8], state: &mut [u32; WIDTH]) {
    let input_len = input.len();
    let padded_len = (input_len + FIELD_SIZE) / FIELD_SIZE * FIELD_SIZE;

    let mut padded_input = Vec::with_capacity(padded_len);
    padded_input.extend_from_slice(input);
    padded_input.resize(padded_len, 0);

    apply_padding(&mut padded_input, input_len, padded_len);
    poseidon2_sponge(&padded_input, state);
}

#[inline(always)]
fn apply_padding(padded_input: &mut [u8], original_len: usize, padded_len: usize) {
    let is_boundary = (original_len % FIELD_SIZE == FIELD_SIZE - 1) as u8;
    padded_input[original_len] = 1 | (is_boundary << 7);

    if is_boundary == 0 {
        padded_input[padded_len - 1] = 0b10000000;
    }
}
