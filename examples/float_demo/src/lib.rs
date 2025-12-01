use hax_lib as hax;

// Type aliases for float arrays
pub type FloatArray3 = [f32; 3];
pub type FloatArray9 = [f32; 9];

/// Initialize a 3-element f32 array with zeros
pub fn init_float_array3_zero() -> FloatArray3 {
    [0.0, 0.0, 0.0]
}

/// Initialize a 3-element f32 array with literal values
pub fn init_float_array3_literal() -> FloatArray3 {
    [1.0, 2.0, 3.0]
}

/// Initialize a 9-element f32 array (for 3x3 matrix)
pub fn init_float_array9_zero() -> FloatArray9 {
    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
}

/// Get element from f32 array
pub fn array_get(arr: &FloatArray3, idx: usize) -> f32 {
    arr[idx]
}

/// Set element in f32 array
pub fn array_set(arr: &mut FloatArray3, idx: usize, value: f32) {
    arr[idx] = value;
}

/// Add two f32 values
pub fn float_add(a: f32, b: f32) -> f32 {
    a + b
}

/// Multiply two f32 values
pub fn float_mul(a: f32, b: f32) -> f32 {
    a * b
}

// ===== Functions with requires/ensures contracts =====

/// Safe division with precondition that divisor is non-zero
#[hax::requires(divisor != 0.0)]
#[hax::ensures(|result| result == numerator / divisor)]
pub fn safe_divide(numerator: f32, divisor: f32) -> f32 {
    numerator / divisor
}

/// Safe array access with bounds checking
#[hax::requires(idx < 3)]
#[hax::ensures(|result| result == arr[idx as usize])]
pub fn safe_array_get(arr: &FloatArray3, idx: usize) -> f32 {
    arr[idx]
}

/// Normalize a value to range [0.0, 1.0]
/// Requires: min < max
/// Ensures: result is in [0.0, 1.0]
#[hax::requires(min < max)]
#[hax::ensures(|result| result >= 0.0 && result <= 1.0)]
pub fn normalize(value: f32, min: f32, max: f32) -> f32 {
    let clamped = if value < min {
        min
    } else if value > max {
        max
    } else {
        value
    };
    (clamped - min) / (max - min)
}

/// Compute average of array elements
/// Ensures: result equals the mathematical average
#[hax::ensures(|result| {
    let sum = arr[0] + arr[1] + arr[2];
    result == sum / 3.0
})]
pub fn array_average(arr: &FloatArray3) -> f32 {
    let sum = arr[0] + arr[1] + arr[2];
    sum / 3.0
}

/// Scale a value by a factor
/// Requires: factor >= 0.0
/// Ensures: result has same sign as input (when input is non-zero)
#[hax::requires(factor >= 0.0)]
#[hax::ensures(|result| {
    (value == 0.0 && result == 0.0) ||
    (value > 0.0 && result >= 0.0) ||
    (value < 0.0 && result <= 0.0)
})]
pub fn scale_value(value: f32, factor: f32) -> f32 {
    value * factor
}

/// Linear interpolation between two values
/// Requires: t is in [0.0, 1.0]
/// Ensures: result is between a and b (when a <= b)
#[hax::requires(t >= 0.0 && t <= 1.0)]
#[hax::ensures(|result| {
    (a <= b && result >= a && result <= b) ||
    (a > b && result <= a && result >= b)
})]
pub fn lerp(a: f32, b: f32, t: f32) -> f32 {
    a + (b - a) * t
}

// ===== End of requires/ensures contracts =====


/// Sum all elements in a f32 array
pub fn array_sum(arr: &FloatArray3) -> f32 {
    let mut sum = 0.0;
    let mut i = 0;
    while i < 3 {
        sum = sum + arr[i];
        i += 1;
    }
    sum
}

/// Dot product of two f32 arrays
pub fn dot_product(a: &FloatArray3, b: &FloatArray3) -> f32 {
    let mut result = 0.0;
    let mut i = 0;
    while i < 3 {
        result = result + a[i] * b[i];
        i += 1;
    }
    result
}

/// Get element from 3x3 matrix stored as flat array (row-major)
pub fn mat_get_simple(mat: &FloatArray9, row: usize, col: usize) -> f32 {
    mat[row * 3 + col]
}

/// Set element in 3x3 matrix stored as flat array (row-major)
pub fn mat_set_simple(mat: &mut FloatArray9, row: usize, col: usize, value: f32) {
    mat[row * 3 + col] = value;
}

/// 3x3 matrix-vector multiplication
/// Multiplies a 3x3 matrix with a 3-element vector
pub fn mat_vec_mul_3x3(mat: &FloatArray9, vec: &FloatArray3) -> FloatArray3 {
    let mut result = [0.0, 0.0, 0.0];
    let mut i = 0;
    while i < 3 {
        let mut sum = 0.0;
        let mut j = 0;
        while j < 3 {
            sum = sum + mat[i * 3 + j] * vec[j];
            j += 1;
        }
        result[i] = sum;
        i += 1;
    }
    result
}

/// 3x3 matrix-matrix multiplication
/// Multiplies two 3x3 matrices
pub fn matmul_3x3(a: &FloatArray9, b: &FloatArray9) -> FloatArray9 {
    let mut result = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
    let mut i = 0;
    while i < 3 {
        let mut j = 0;
        while j < 3 {
            let mut sum = 0.0;
            let mut k = 0;
            while k < 3 {
                sum = sum + a[i * 3 + k] * b[k * 3 + j];
                k += 1;
            }
            result[i * 3 + j] = sum;
            j += 1;
        }
        i += 1;
    }
    result
}

/// More complex example: matrix multiplication with f64
pub type DoubleMatrix4 = [f64; 16];

/// 4x4 matrix multiplication with f64
pub fn matmul_4x4_f64(a: &DoubleMatrix4, b: &DoubleMatrix4) -> DoubleMatrix4 {
    let mut result = [0.0; 16];
    let mut i = 0;
    while i < 4 {
        let mut j = 0;
        while j < 4 {
            let mut sum = 0.0;
            let mut k = 0;
            while k < 4 {
                sum = sum + a[i * 4 + k] * b[k * 4 + j];
                k += 1;
            }
            result[i * 4 + j] = sum;
            j += 1;
        }
        i += 1;
    }
    result
}

/// Test float operations with mixed arithmetic
pub fn mixed_float_ops(x: f32, y: f32, z: f32) -> f32 {
    let temp1 = x * y;
    let temp2 = temp1 + z;
    let temp3 = temp2 * 2.0;
    temp3 - x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_and_access() {
        let arr = init_float_array3_literal();
        assert_eq!(arr[0], 1.0);
        assert_eq!(arr[1], 2.0);
        assert_eq!(arr[2], 3.0);
    }

    #[test]
    fn test_array_operations() {
        let mut arr = init_float_array3_zero();
        array_set(&mut arr, 0, 5.0);
        array_set(&mut arr, 1, 10.0);
        array_set(&mut arr, 2, 15.0);

        assert_eq!(array_get(&arr, 0), 5.0);
        assert_eq!(array_get(&arr, 1), 10.0);
        assert_eq!(array_get(&arr, 2), 15.0);
    }

    #[test]
    fn test_sum() {
        let arr = [1.0, 2.0, 3.0];
        let sum = array_sum(&arr);
        assert_eq!(sum, 6.0);
    }

    #[test]
    fn test_dot_product() {
        let a = [1.0, 2.0, 3.0];
        let b = [4.0, 5.0, 6.0];
        let result = dot_product(&a, &b);
        assert_eq!(result, 32.0); // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
    }

    #[test]
    fn test_matrix_get_set() {
        let mut mat = init_float_array9_zero();
        mat_set_simple(&mut mat, 0, 0, 1.0);
        mat_set_simple(&mut mat, 1, 1, 2.0);
        mat_set_simple(&mut mat, 2, 2, 3.0);

        assert_eq!(mat_get_simple(&mat, 0, 0), 1.0);
        assert_eq!(mat_get_simple(&mat, 1, 1), 2.0);
        assert_eq!(mat_get_simple(&mat, 2, 2), 3.0);
    }

    #[test]
    fn test_mat_vec_mul() {
        // Identity matrix
        let mat = [
            1.0, 0.0, 0.0,
            0.0, 1.0, 0.0,
            0.0, 0.0, 1.0,
        ];
        let vec = [2.0, 3.0, 4.0];
        let result = mat_vec_mul_3x3(&mat, &vec);

        assert_eq!(result[0], 2.0);
        assert_eq!(result[1], 3.0);
        assert_eq!(result[2], 4.0);
    }

    #[test]
    fn test_matmul() {
        // Identity matrix times any matrix should return the same matrix
        let identity = [
            1.0, 0.0, 0.0,
            0.0, 1.0, 0.0,
            0.0, 0.0, 1.0,
        ];
        let mat = [
            2.0, 3.0, 4.0,
            5.0, 6.0, 7.0,
            8.0, 9.0, 10.0,
        ];
        let result = matmul_3x3(&identity, &mat);

        for i in 0..9 {
            assert_eq!(result[i], mat[i]);
        }
    }

    #[test]
    fn test_mixed_ops() {
        let result = mixed_float_ops(2.0, 3.0, 1.0);
        // (2.0 * 3.0 + 1.0) * 2.0 - 2.0 = (6.0 + 1.0) * 2.0 - 2.0 = 7.0 * 2.0 - 2.0 = 14.0 - 2.0 = 12.0
        assert_eq!(result, 12.0);
    }

    // Tests for requires/ensures contracts
    #[test]
    fn test_safe_divide() {
        let result = safe_divide(10.0, 2.0);
        assert_eq!(result, 5.0);

        let result = safe_divide(7.0, 2.0);
        assert_eq!(result, 3.5);
    }

    #[test]
    fn test_safe_array_get() {
        let arr = [1.0, 2.0, 3.0];
        assert_eq!(safe_array_get(&arr, 0), 1.0);
        assert_eq!(safe_array_get(&arr, 1), 2.0);
        assert_eq!(safe_array_get(&arr, 2), 3.0);
    }

    #[test]
    fn test_normalize() {
        // Value in middle of range
        let result = normalize(5.0, 0.0, 10.0);
        assert_eq!(result, 0.5);

        // Value at min
        let result = normalize(0.0, 0.0, 10.0);
        assert_eq!(result, 0.0);

        // Value at max
        let result = normalize(10.0, 0.0, 10.0);
        assert_eq!(result, 1.0);

        // Value below min (should clamp)
        let result = normalize(-5.0, 0.0, 10.0);
        assert_eq!(result, 0.0);

        // Value above max (should clamp)
        let result = normalize(15.0, 0.0, 10.0);
        assert_eq!(result, 1.0);
    }

    #[test]
    fn test_array_average() {
        let arr = [3.0, 6.0, 9.0];
        let avg = array_average(&arr);
        assert_eq!(avg, 6.0);

        let arr = [1.0, 2.0, 3.0];
        let avg = array_average(&arr);
        assert_eq!(avg, 2.0);
    }

    #[test]
    fn test_scale_value() {
        assert_eq!(scale_value(5.0, 2.0), 10.0);
        assert_eq!(scale_value(-5.0, 2.0), -10.0);
        assert_eq!(scale_value(0.0, 2.0), 0.0);
        assert_eq!(scale_value(5.0, 0.0), 0.0);
    }

    #[test]
    fn test_lerp() {
        // t=0 should return a
        assert_eq!(lerp(0.0, 10.0, 0.0), 0.0);

        // t=1 should return b
        assert_eq!(lerp(0.0, 10.0, 1.0), 10.0);

        // t=0.5 should return midpoint
        assert_eq!(lerp(0.0, 10.0, 0.5), 5.0);

        // Works with negative values
        assert_eq!(lerp(-10.0, 10.0, 0.5), 0.0);
    }
}
