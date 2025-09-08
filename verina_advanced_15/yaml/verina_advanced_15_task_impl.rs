use vstd::prelude::*;

verus! {
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
{
    let n = nums.len();
    
    for i in 0..n
        invariant
            forall|ii: int, jj: int, kk: int|
                0 <= ii < i && ii < jj && jj < kk < n ==>
                !(nums[ii] < nums[jj] && nums[jj] < nums[kk])
    {
        for j in (i + 1)..n
            invariant
                i < n,
                forall|ii: int, jj: int, kk: int|
                    0 <= ii < i && ii < jj && jj < kk < n ==>
                    !(nums[ii] < nums[jj] && nums[jj] < nums[kk]),
                forall|jj: int, kk: int|
                    (i + 1) <= jj < j && jj < kk < n ==>
                    !(nums[i as int] < nums[jj] && nums[jj] < nums[kk])
        {
            for k in (j + 1)..n
                invariant
                    i < j < n,
                    forall|ii: int, jj: int, kk: int|
                        0 <= ii < i && ii < jj && jj < kk < n ==>
                        !(nums[ii] < nums[jj] && nums[jj] < nums[kk]),
                    forall|jj: int, kk: int|
                        (i + 1) <= jj < j && jj < kk < n ==>
                        !(nums[i as int] < nums[jj] && nums[jj] < nums[kk]),
                    forall|kk: int|
                        (j + 1) <= kk < k ==>
                        !(nums[i as int] < nums[j as int] && nums[j as int] < nums[kk])
            {
                /* code modified by LLM (iteration 3): add bounds assertions and use proper bounds checks */
                proof {
                    assert(i < n);
                    assert(j < n);
                    assert(k < n);
                    assert(0 <= i < j && j < k < nums.len());
                }
                if nums[i] < nums[j] && nums[j] < nums[k] {
                    return true;
                }
            }
        }
    }
    
    false
}
}

fn main() {
    /*
    -- Invalid Inputs
    []
    -- Tests
    [
        {
            "input": {
                "nums": "[1, 2, 3]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "nums": "[5, 4, 3, 2, 1]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "nums": "[2, 1, 5, 0, 4, 6]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "nums": "[1, 5, 0, 4, 1, 3]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "nums": "[5, 4, 3]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "nums": "[]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        }
    ]
    */
}