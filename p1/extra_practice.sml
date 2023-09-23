(* alternating + and - function *)

(* problem1 *)		  
fun alternate (xs : int list) =
    if null xs
    then 0
    else if null (tl xs)
    then hd xs
    else
    let
	fun alternate_sum_without_first(xs : int list) =
	    if null (tl xs) orelse null (tl (tl xs))
	    then ~(hd xs)
	    else ~(hd xs) +  alternate_sum_without_first(tl (tl xs))
							
	fun alternate_sum(xs : int list) =
	    if null (tl xs) orelse null (tl (tl xs))
	    then hd xs
	    else hd xs + alternate_sum(tl (tl xs))
    in
	alternate_sum_without_first(tl xs) + alternate_sum(xs)
    end
	
(* problem2 *)
fun min_max(xs : int list) =
    if null xs
    then NONE
    else
	let
	    fun max_nonempty(xs : int list) =
		if null (tl xs)
		then hd xs
		else
		    let val tl_ans = max_nonempty(tl xs)
		    in
			if hd xs > tl_ans
			then hd xs
			else tl_ans
		    end

	    fun min_nonempty(xs : int list) =
		 if null (tl xs)
		 then hd xs
		 else
		     let val tl_ans = min_nonempty(tl xs)
		     in
			 if hd xs < tl_ans
			 then hd xs
			 else tl_ans
		     end
	in
	    SOME (min_nonempty(xs), max_nonempty(xs))
	end
	    
	    (* Problem3 *)
fun cumsum (xs : int list) =
    if null xs
    then []
    else  if null (tl (tl xs))
    then hd xs :: ((hd xs) + hd (tl xs)) :: []
    else if null (tl xs)
    then hd xs :: []
    else let val ys = hd xs :: (hd xs + hd (tl xs)) :: []
	     val vs = ys
			  
	     fun update_list (ms : int list, x : int, y : int) =
		 ms @ [x+y]
				
	     fun p_sum (xs : int list, ys : int list) =
		 if null xs orelse null (tl (tl xs))
		 then []
		 else hd (tl ys) + hd (tl (tl xs)) :: p_sum(tl xs, tl (update_list (ys, hd (tl ys),hd (tl (tl xs)))))

	 in
	    vs @ p_sum (xs, ys)
	 end

fun greeting (str_op : string option) =
    if isSome str_op
    then "Hello there, " ^ valOf str_op ^ "!"
    else "Hello there, you!"

fun repeat (nums : int list, pos_nums : int list) =
    let fun repeat_each(num : int, pos_num : int) =
	if pos_num = 0
	then []
	else num :: repeat_each (num, pos_num -1)
    in
	if null nums orelse null pos_nums
	then []
	else repeat_each(hd nums, hd pos_nums) @ repeat (tl nums, tl pos_nums)
    end

fun addOpt (x : int option, y : int option) =
	   if isSome x  andalso isSome y
	   then SOME (valOf x + valOf y)
	   else NONE

fun addAllOpt (xs : (int option) list) =
    let fun addOpt(x : int option, y : int option) =
	    if isSome x andalso isSome y
	    then SOME (valOf x + valOf y)
	    else if isSome x
	    then SOME (valOf x)
	    else if isSome y
	    then SOME (valOf y)
	    else NONE

	fun helper(res : int option, xs : (int option) list) =
	    if null xs
	    then res
	    else helper(addOpt(res, hd xs), tl xs)
    in
	helper(NONE, xs)
    end

fun any (xs : bool list) =
    if null xs
    then false
    else hd xs orelse any(tl xs)

fun all (xs : bool list) =
    let fun all_helper(res : bool, xs : bool list) =
	    if null xs
	    then res
	    else all_helper(res andalso hd xs, tl xs)
    in
	all_helper(true, xs)
    end
    
fun zip (xs : int list, ys : int list) =
    if null xs orelse null ys
    then []
    else (hd xs, hd ys) :: zip(tl xs, tl ys)

fun is_longer (l1 : int list, l2 : int list) =
    length l1 > length l2

fun zipRecycle (xs : int list, ys : int list) =
    let
	fun normalise (l1 : int list, l2 : int list) =
	    let val is_l1_longer = is_longer(l1,l2)
		val longer_one = if is_l1_longer then l1 else l2
		val shorter_one = if is_l1_longer then l2 else l1
								   
		fun match (shorter : int list) =
		    if is_longer(shorter, longer_one)
		    then shorter
		    else match(shorter @ shorter_one)
			      
	    in
		if is_l1_longer
		then (l1, match l2)
		else (match l1, l2)
	    end
    in
	zip(normalise(xs,ys))
    end
	
fun zipOpt (xs : int list, ys : int list) =
    if length xs = length ys
    then SOME (zip (xs,ys))
    else NONE

fun lookup (xs : (string * int) list, x : string) =
    if null xs
    then NONE
    else if #1 (hd xs) = x
    then SOME (#2 (hd xs))
    else lookup(tl xs, x)

fun all_grt (xs : int list, threshold : int) =
    if null xs
    then []
    else if hd xs >= threshold
    then hd xs :: all_grt(tl xs,threshold)
    else all_grt(tl xs,threshold)

fun all_lst (xs : int list, threshold : int) =
    if null xs
    then []
    else if hd xs < threshold
    then hd xs :: all_lst(tl xs,threshold)
    else all_lst(tl xs,threshold)

fun splitup (xs : int list) =
    (all_lst(xs,0),all_grt(xs,0))

fun splitAt (xs : int list, threshold : int) =
    (all_lst(xs, threshold),all_grt(xs, threshold))

fun isSorted (xs : int list) =
    null xs orelse null (tl xs) orelse hd xs < hd (tl xs) andalso isSorted(tl xs)

fun isAnySorted (xs : int list) =
    isSorted(xs) orelse (null xs orelse null (tl xs) orelse hd xs > hd (tl xs) andalso isAnySorted(tl xs))

fun sortedMerge (xs : int list, ys : int list) =
    if null xs
    then ys
    else if null ys
    then xs
    else if hd xs <= hd ys
    then hd xs :: sortedMerge(tl xs, ys)
    else hd ys :: sortedMerge(xs, tl ys)

fun qsort (xs : int list) =
    if null xs orelse null (tl xs)
    then xs
    else
	let val split_list = splitAt(tl xs, hd xs)
	    val sort1 = qsort(#1 split_list)
	    val sort2 = qsort(#2 split_list)
	in
	    sort1 @ [hd xs] @ sort2
	end

fun divide (xs : int list) =
    let fun divide_helper (xs : int list, firsts : int list, seconds : int list) =
	    if null xs
	    then (firsts,seconds)
	    else let val l1 = divide_helper(tl xs, firsts, seconds)
		 in
		     (hd xs :: (#2 l1), #1 l1)
		 end
    in
	divide_helper(xs,[],[])
    end

fun not_so_quick_sort (xs : int list) =
    if null xs orelse null (tl xs)
    then xs
    else let val split_list = splitAt(tl xs, hd xs)
	     val l_list = not_so_quick_sort(#1 split_list)
	     val r_list = not_so_quick_sort(#2 split_list)
	 in
	     sortedMerge(l_list, r_list)
	 end

fun fullDivide (k : int, n : int) =
    if n mod k <> 0
    then (0, n)
    else let val rdiv = fullDivide(k, n div k)
	 in
	     (1 + #1 rdiv, #2 rdiv)
	 end
    
fun factorize (n : int) =
    let fun factorize_helper(k : int, n : int) =
	    if k > n
	    then []
	    else let val gen_prime = fullDivide(k,n)
		 in
		     if #1 gen_prime = 0
		     then factorize_helper(k + 1, #2 gen_prime)
		     else (k, #1 gen_prime) :: factorize_helper(k + 1, #2 gen_prime)
		 end
    in
	factorize_helper(2, n)
    end

fun multiply (factors : (int * int) list) =
    let fun pow (n : int, k : int) =
	    if k = 0
	    then 1
	    else n * pow(n, k-1)
    in
	
    if null factors
    then 1
    else pow(hd factors) * multiply(tl factors)
    end
