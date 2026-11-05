use crate::{RATE, WIDTH};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear;
use p3_symmetric::Permutation;
use zkm_primitives::poseidon2_init;

#[inline]
pub(crate) fn poseidon2_sponge(padded_input: &[u8], input_state: &mut [u32; WIDTH]) {
    let input = bytes_to_field_elements(&padded_input);
    let input = input
        .iter()
        .map(|&x| KoalaBear::from_u32(x))
        .collect::<Vec<_>>();
    let mut state = input_state.map(KoalaBear::from_u32);
    let mut chunks = input.chunks_exact(RATE);

    let hasher = poseidon2_init();
    for chunk in &mut chunks {
        state[..RATE].clone_from_slice(chunk);
        hasher.permute_mut(&mut state);
    }

    let remainder = chunks.remainder();
    if !remainder.is_empty() {
        state[..remainder.len()].clone_from_slice(remainder);
        hasher.permute_mut(&mut state);
    }

    for i in 0..WIDTH {
        input_state[i] = state[i].as_canonical_u32();
    }
}

// each 3 bytes of input can be safely converted to a field element
#[inline]
fn bytes_to_field_elements(bytes: &[u8]) -> Vec<u32> {
    bytes
        .chunks(3)
        .map(|chunk| {
            let mut value = 0u32;
            for (i, &byte) in chunk.iter().enumerate() {
                value |= (byte as u32) << (i * 8);
            }
            value
        })
        .collect()
}
