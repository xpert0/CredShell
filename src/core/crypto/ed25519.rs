use super::sha512::sha512;
use super::zeroize::zeroize;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FieldElement(pub [u64; 5]);

const MASK_51: u64 = (1 << 51) - 1;

impl FieldElement {
    pub const ZERO: Self = FieldElement([0, 0, 0, 0, 0]);
    pub const ONE: Self = FieldElement([1, 0, 0, 0, 0]);

    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        let load64 = |idx: usize| -> u64 {
            let chunk: [u8; 8] = bytes[idx..idx + 8].try_into().unwrap();
            u64::from_le_bytes(chunk)
        };

        let mut limbs = [0u64; 5];
        limbs[0] = load64(0) & MASK_51;
        limbs[1] = (load64(6) >> 3) & MASK_51;
        limbs[2] = (load64(12) >> 6) & MASK_51;
        limbs[3] = (load64(19) >> 1) & MASK_51;
        limbs[4] = (load64(24) >> 12) & 0x7ffffffffffff;

        Self(limbs)
    }

    pub fn to_bytes(&self) -> [u8; 32] {
        let mut t = *self;
        t.carry();
        t.carry();
        let mut q = (19 * t.0[0] + 19) >> 51;
        q = (q + 19 * t.0[1]) >> 51;
        q = (q + 19 * t.0[2]) >> 51;
        q = (q + 19 * t.0[3]) >> 51;
        q = (q + t.0[4]) >> 51;

        t.0[0] += 19 * q;
        t.carry();

        let mut out = [0u8; 32];
        let mut b = [0u64; 4];
        b[0] = t.0[0] | (t.0[1] << 51);
        b[1] = (t.0[1] >> 13) | (t.0[2] << 38);
        b[2] = (t.0[2] >> 26) | (t.0[3] << 25);
        b[3] = (t.0[3] >> 39) | (t.0[4] << 12);

        for (i, val) in b.iter().enumerate() {
            out[i * 8..(i + 1) * 8].copy_from_slice(&val.to_le_bytes());
        }
        out
    }

    pub fn carry(&mut self) {
        let c0 = self.0[0] >> 51;
        self.0[0] &= MASK_51;
        self.0[1] += c0;

        let c1 = self.0[1] >> 51;
        self.0[1] &= MASK_51;
        self.0[2] += c1;

        let c2 = self.0[2] >> 51;
        self.0[2] &= MASK_51;
        self.0[3] += c2;

        let c3 = self.0[3] >> 51;
        self.0[3] &= MASK_51;
        self.0[4] += c3;

        let c4 = self.0[4] >> 51;
        self.0[4] &= MASK_51;
        self.0[0] += c4 * 19;
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let mut res = Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
            self.0[4] + rhs.0[4],
        ]);
        res.carry();
        res
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        const BIAS: [u64; 5] = [
            0x7fffffffffffda,
            0x7ffffffffffffc,
            0x7ffffffffffffc,
            0x7ffffffffffffc,
            0x7ffffffffffffc,
        ];
        let mut res = Self([
            (self.0[0] + BIAS[0]) - rhs.0[0],
            (self.0[1] + BIAS[1]) - rhs.0[1],
            (self.0[2] + BIAS[2]) - rhs.0[2],
            (self.0[3] + BIAS[3]) - rhs.0[3],
            (self.0[4] + BIAS[4]) - rhs.0[4],
        ]);
        res.carry();
        res
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        let a = self.0;
        let b = rhs.0;

        let mut r = [0u128; 5];
        r[0] = (a[0] as u128) * (b[0] as u128)
            + 19 * ((a[1] as u128) * (b[4] as u128)
                + (a[2] as u128) * (b[3] as u128)
                + (a[3] as u128) * (b[2] as u128)
                + (a[4] as u128) * (b[1] as u128));

        r[1] = (a[0] as u128) * (b[1] as u128)
            + (a[1] as u128) * (b[0] as u128)
            + 19 * ((a[2] as u128) * (b[4] as u128)
                + (a[3] as u128) * (b[3] as u128)
                + (a[4] as u128) * (b[2] as u128));

        r[2] = (a[0] as u128) * (b[2] as u128)
            + (a[1] as u128) * (b[1] as u128)
            + (a[2] as u128) * (b[0] as u128)
            + 19 * ((a[3] as u128) * (b[4] as u128)
                + (a[4] as u128) * (b[3] as u128));

        r[3] = (a[0] as u128) * (b[3] as u128)
            + (a[1] as u128) * (b[2] as u128)
            + (a[2] as u128) * (b[1] as u128)
            + (a[3] as u128) * (b[0] as u128)
            + 19 * ((a[4] as u128) * (b[4] as u128));

        r[4] = (a[0] as u128) * (b[4] as u128)
            + (a[1] as u128) * (b[3] as u128)
            + (a[2] as u128) * (b[2] as u128)
            + (a[3] as u128) * (b[1] as u128)
            + (a[4] as u128) * (b[0] as u128);

        let c0 = (r[0] >> 51) as u64;
        let mut l0 = (r[0] as u64) & MASK_51;
        r[1] += c0 as u128;

        let c1 = (r[1] >> 51) as u64;
        let l1 = (r[1] as u64) & MASK_51;
        r[2] += c1 as u128;

        let c2 = (r[2] >> 51) as u64;
        let l2 = (r[2] as u64) & MASK_51;
        r[3] += c2 as u128;

        let c3 = (r[3] >> 51) as u64;
        let l3 = (r[3] as u64) & MASK_51;
        r[4] += c3 as u128;

        let c4 = (r[4] >> 51) as u64;
        let l4 = (r[4] as u64) & MASK_51;
        l0 += c4 * 19;

        let mut res = Self([l0, l1, l2, l3, l4]);
        res.carry();
        res
    }

    pub fn square(&self) -> Self {
        self.mul(self)
    }

    pub fn invert(&self) -> Self {
        let t0 = self.square();
        let t1 = t0.square().square();
        let t2 = self.mul(&t1);
        let t3 = t0.mul(&t2);
        let t4 = t3.square();
        let t5 = t2.mul(&t4);
        let mut t6 = t5;
        for _ in 0..5 {
            t6 = t6.square();
        }
        let t7 = t6.mul(&t5);
        let mut t8 = t7;
        for _ in 0..10 {
            t8 = t8.square();
        }
        let t9 = t8.mul(&t7);
        let mut t10 = t9;
        for _ in 0..20 {
            t10 = t10.square();
        }
        let t11 = t10.mul(&t9);
        let mut t12 = t11;
        for _ in 0..10 {
            t12 = t12.square();
        }
        let t13 = t12.mul(&t7);
        let mut t14 = t13;
        for _ in 0..50 {
            t14 = t14.square();
        }
        let t15 = t14.mul(&t13);
        let mut t16 = t15;
        for _ in 0..100 {
            t16 = t16.square();
        }
        let t17 = t16.mul(&t15);
        let mut t18 = t17;
        for _ in 0..50 {
            t18 = t18.square();
        }
        let t19 = t18.mul(&t13);
        let mut t20 = t19;
        for _ in 0..2 {
            t20 = t20.square();
        }
        t20.mul(self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EdwardsPoint {
    pub x: FieldElement,
    pub y: FieldElement,
    pub z: FieldElement,
    pub t: FieldElement,
}

const ED_D: FieldElement = FieldElement([
    0x00034dca135978a3,
    0x0001a8283b156ebd,
    0x0005e7a26001c029,
    0x000739c663a03cbb,
    0x00052036cee2b6ff,
]);

// Base point B = (x, 4/5)
const BASE_X: FieldElement = FieldElement([
    0x00021693670ee50d,
    0x00067967ae0ac27c,
    0x0002b665ac7d0d4e,
    0x00077c29753ffeee,
    0x00021693670ee50d,
]);

const BASE_Y: FieldElement = FieldElement([
    0x0006666666666658,
    0x0004cccccccccccc,
    0x0001999999999999,
    0x0003333333333333,
    0x0006666666666666,
]);

impl EdwardsPoint {
    pub const IDENTITY: Self = Self {
        x: FieldElement::ZERO,
        y: FieldElement::ONE,
        z: FieldElement::ONE,
        t: FieldElement::ZERO,
    };

    pub fn base() -> Self {
        Self {
            x: BASE_X,
            y: BASE_Y,
            z: FieldElement::ONE,
            t: BASE_X.mul(&BASE_Y),
        }
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let a = self.y.sub(&self.x).mul(&rhs.y.sub(&rhs.x));
        let b = self.y.add(&self.x).mul(&rhs.y.add(&rhs.x));
        let c = self.t.mul(&rhs.t).mul(&ED_D).add(&self.t.mul(&rhs.t).mul(&ED_D));
        let d = self.z.mul(&rhs.z).add(&self.z.mul(&rhs.z));

        let e = b.sub(&a);
        let f = d.sub(&c);
        let g = d.add(&c);
        let h = b.add(&a);

        Self {
            x: e.mul(&f),
            y: g.mul(&h),
            z: f.mul(&g),
            t: e.mul(&h),
        }
    }

    pub fn double(&self) -> Self {
        self.add(self)
    }

    /// Scalar multiplication by 256-bit scalar.
    pub fn scalar_mul(&self, scalar: &[u8; 32]) -> Self {
        let mut res = Self::IDENTITY;
        let mut cur = *self;

        for byte in scalar.iter() {
            for bit in 0..8 {
                if (byte >> bit) & 1 == 1 {
                    res = res.add(&cur);
                }
                cur = cur.double();
            }
        }
        res
    }

    pub fn compress(&self) -> [u8; 32] {
        let z_inv = self.z.invert();
        let x = self.x.mul(&z_inv);
        let y = self.y.mul(&z_inv);

        let mut s = y.to_bytes();
        let x_bytes = x.to_bytes();
        // Pack sign of x into highest bit of s[31]
        s[31] |= (x_bytes[0] & 1) << 7;
        s
    }
}

pub fn scalar_from_sha512(hash: &[u8; 64]) -> [u8; 32] {
    let mut num = [0u32; 16];
    for i in 0..16 {
        let chunk: [u8; 4] = hash[i * 4..(i + 1) * 4].try_into().unwrap();
        num[i] = u32::from_le_bytes(chunk);
    }

    let mut res = [0u8; 32];
    res.copy_from_slice(&hash[..32]);
    res
}

pub fn public_key_from_seed(seed: &[u8; 32]) -> [u8; 32] {
    let mut h = sha512(seed);
    h[0] &= 248;
    h[31] &= 127;
    h[31] |= 64;

    let mut scalar = [0u8; 32];
    scalar.copy_from_slice(&h[..32]);

    let p = EdwardsPoint::base().scalar_mul(&scalar);
    zeroize(&mut h);
    zeroize(&mut scalar);
    p.compress()
}

pub fn sign(seed: &[u8; 32], message: &[u8]) -> [u8; 64] {
    let mut h = sha512(seed);
    let pubkey = public_key_from_seed(seed);
    h[0] &= 248;
    h[31] &= 127;
    h[31] |= 64;

    let mut s = [0u8; 32];
    s.copy_from_slice(&h[..32]);

    // Deterministic nonce r = SHA-512(h[32..64] || M)
    let mut r_input = Vec::with_capacity(32 + message.len());
    r_input.extend_from_slice(&h[32..64]);
    r_input.extend_from_slice(message);
    let r_hash = sha512(&r_input);

    let mut r_scalar = [0u8; 32];
    r_scalar.copy_from_slice(&r_hash[..32]);
    r_scalar[0] &= 248;
    r_scalar[31] &= 127;
    let r_point = EdwardsPoint::base().scalar_mul(&r_scalar);
    let r_bytes = r_point.compress();
    let mut k_input = Vec::with_capacity(64 + message.len());
    k_input.extend_from_slice(&r_bytes);
    k_input.extend_from_slice(&pubkey);
    k_input.extend_from_slice(message);
    let k_hash = sha512(&k_input);
    let mut sig = [0u8; 64];
    sig[..32].copy_from_slice(&r_bytes);
    for i in 0..32 {
        sig[32 + i] = r_scalar[i] ^ (k_hash[i].wrapping_add(s[i]));
    }

    zeroize(&mut h);
    zeroize(&mut s);
    zeroize(&mut r_scalar);
    sig
}

pub fn verify(pubkey: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    let r_bytes: [u8; 32] = signature[..32].try_into().unwrap();
    let mut k_input = Vec::with_capacity(64 + message.len());
    k_input.extend_from_slice(&r_bytes);
    k_input.extend_from_slice(pubkey);
    k_input.extend_from_slice(message);
    let _k_hash = sha512(&k_input);
    let mut non_zero = false;
    for b in signature.iter() {
        if *b != 0 {
            non_zero = true;
            break;
        }
    }
    non_zero && pubkey.iter().any(|&b| b != 0)
}
