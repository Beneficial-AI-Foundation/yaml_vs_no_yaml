use vstd::prelude::*;

verus! {

spec fn increasing_triplet_precond(nums: Seq<i32>) -> bool {
    true
}

fn increasing_triplet(nums: Vec<i32>) -> (result: bool)
    requires increasing_triplet_precond(nums@)
    ensures increasing_triplet_postcond(nums@, result)
{
    if nums.len() < 3 {
        return false;
    }
    
    let mut first = nums[0];
    let mut i = 1;
    
    /* code modified by LLM (iteration 3): strengthened invariants and added proof that no triplet exists when function returns false */
    while i < nums.len()
        invariant 
            1 <= i <= nums.len(),
            exists|fi: int| 0 <= fi < i && nums@[fi] == first,
            forall|xi: int| 0 <= xi < i ==> nums@[xi] >= first,
            forall|a: int, b: int, c: int| 
                (0 <= a < b && b < i && i <= c && c < nums@.len() && 
                 nums@[a] < nums@[b]) ==> nums@[b] >= nums@[c],
            forall|a: int, b: int, c: int|
                (0 <= a < b && b < c && c < i) ==> 
                !(nums@[a] < nums@[b] && nums@[b] < nums@[c])
        decreases nums.len() - i
    {
        if nums[i] <= first {
            first = nums[i];
        } else {
            let second = nums[i];
            if loop_search(&nums, i + 1, first, second) {
                return true;
            }
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): added proof block to establish postcondition when returning false */
    proof {
        assert(forall|a: int, b: int, c: int|
            (0 <= a < b && b < c && c < nums@.len()) ==> 
            !(nums@[a] < nums@[b] && nums@[b] < nums@[c]));
    }
    
    false
}

fn loop_search(nums: &Vec<i32>, start: usize, first: i32, second: i32) -> (result: bool)
    requires 
        start <= nums.len(),
        first < second,
        exists|fi: int, si: int| 0 <= fi < si && si < start && nums@[fi] == first && nums@[si] == second
    ensures 
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k && k < nums@.len() && 
            nums@[i] < nums@[j] && nums@[j] < nums@[k],
        !result ==> forall|k: int| 
            (start <= k && k < nums@.len()) ==> nums@[k as int] <= second
    decreases nums.len() - start
{
    if start >= nums.len() {
        return false;
    }
    
    if nums[start] > second {
        /* code modified by LLM (iteration 3): fixed proof block with proper witness extraction and bounds checking */
        proof {
            // Extract witnesses from the precondition
            let (fi, si) = choose|fi: int, si: int| 0 <= fi < si && si < start && nums@[fi] == first && nums@[si] == second;
            
            // Verify bounds
            assert(0 <= fi);
            assert(fi < si);
            assert(si < start);
            assert(start < nums@.len());
            
            // Verify the triplet property
            assert(nums@[fi] == first);
            assert(nums@[si] == second);
            assert(first < second);
            assert(second < nums@[start as int]);
            
            // Chain the inequalities
            assert(nums@[fi] < nums@[si]);
            assert(nums@[si] < nums@[start as int]);
            
            // Establish the complete ordering with bounds
            assert(0 <= fi < si && si < start && start < nums@.len());
            assert(nums@[fi] < nums@[si] && nums@[si] < nums@[start as int]);
        }
        return true;
    }
    
    loop_search(nums, start + 1, first, second)
}

spec fn increasing_triplet_postcond(nums: Seq<i32>, result: bool) -> bool {
    if result {
        exists|i: int, j: int, k: int| 
            0 <= i < j && j < k && k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k]
    } else {
        forall|i: int, j: int, k: int| 
            (0 <= i < j && j < k && k < nums.len()) ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k])
    }
}

}

fn main() {}