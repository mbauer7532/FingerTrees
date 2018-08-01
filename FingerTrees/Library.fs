namespace FingerTrees

module FingerTrees =

    let rev f = fun x y -> f y x

    type 'a FingerTree =
        | Empty
        | Single of 'a
        | Deep of ('a Digit * 'a Node FingerTree * 'a Digit)

    and 'a Node =
        | Node2 of 'a * 'a
        | Node3 of 'a * 'a * 'a

    and 'a Digit =
       | D1 of 'a
       | D2 of 'a * 'a
       | D3 of 'a * 'a * 'a
       | D4 of 'a * 'a * 'a * 'a

    let deep leftDigit innerTree rightDigit = Deep (leftDigit, innerTree, rightDigit)
    let node2 x y = Node2 (x, y)
    let node3 x y z = Node3 (x, y, z)

    let digitAddLeft a = function
    | D1 b -> D2 (a, b)
    | D2 (b, c) -> D3 (a, b, c)
    | D3 (b, c, d) -> D4 (a, b, c, d)
    | D4 _ ->  failwith "Should never be called on a D4."

    let digitAddRight a = function
    | D1 b -> D2 (b, a)
    | D2 (c, b) -> D3 (c, b, a)
    | D3 (d, c, b) -> D4 (d, c, b, a)
    | D4 _ ->  failwith "Should never be called on a D4."

    let rec addLeft<'a> (a: 'a) (ft: FingerTree<'a>): FingerTree<'a> =
       match ft with
       | Empty -> Single a
       | Single b -> deep (D1 a) Empty (D1 b)
       | Deep (D4 (b, c, d, e), m, sf) ->
           deep (D2 (a, b)) (addLeft (Node3 (c, d, e)) m) sf
       | Deep (pr, m, sf) -> deep (digitAddLeft a pr) m sf

    let addLeftToFingerTree (ls: 'a List) ft = List.foldBack addLeft ls ft

    let rec addRight<'a> (a: 'a) (ft: FingerTree<'a>): FingerTree<'a> =
       match ft with
       | Empty -> Single a
       | Single b -> deep (D1 b) Empty (D1 a)
       | Deep (pr, m, D4 (e, d, c, b)) ->
           deep pr (addRight (Node3 (e, d, c)) m) (D2 (b, a))
       | Deep (pr, m, sf) -> deep pr m (digitAddRight a sf)

    let addRightToFingerTree (ls: 'a List) ft = List.fold (rev addRight) ft ls
    
    let digitToTree digit =
        match digit with
        | D1 a -> Single a
        | D2 (a, b) -> deep (D1 a) Empty (D1 b)
        | D3 (a, b, c) -> deep (D2 (a, b)) Empty (D1 c)
        | D4 (a, b, c, d) -> deep (D2 (a, b)) Empty (D2 (c, d))

    let nodeToDigit = function
    | Node2 (a, b) -> D2 (a, b)
    | Node3 (a, b, c) -> D3 (a, b, c)

    type 'a viewL =
        | EmptyTreeL
        | ConsL of ('a * 'a FingerTree)

    let rec viewL<'a> (ft : 'a FingerTree): 'a viewL =
        match ft with
        | Empty -> EmptyTreeL
        | Single a -> ConsL (a, Empty)
        | Deep (D4 (a, b, c, d), m, sf) -> ConsL (a, deep (D3 (b, c, d)) m sf)
        | Deep (D3 (a, b, c), m, sf) -> ConsL (a, deep (D2 (b, c)) m sf)
        | Deep (D2 (a, b), m, sf) -> ConsL (a, deep (D1 b) m sf)
        | Deep (D1 a, m, sf) -> ConsL (a, rotateL m sf)

    and rotateL (m: 'a Node FingerTree) (sf: 'a Digit): 'a FingerTree =
        match viewL m with
        | EmptyTreeL -> digitToTree sf
        | ConsL (a, m') -> deep (nodeToDigit a) m' sf

    type 'a viewR =
        | EmptyTreeR
        | ConsR of ('a * 'a FingerTree)

    let rec viewR<'a> (ft : 'a FingerTree): 'a viewR =
        match ft with
        | Empty -> EmptyTreeR
        | Single a -> ConsR (a, Empty)
        | Deep (pr, m, D1 a) -> ConsR (a, rotateR m pr)
        | Deep (pr, m, D2 (b, a)) -> ConsR (a, deep pr m (D1 b))
        | Deep (pr, m, D3 (c, b, a)) -> ConsR (a, deep pr m (D2 (c, b)))
        | Deep (pr, m, D4 (d, c, b, a)) -> ConsR (a, deep pr m (D3 (d, c, b)))

    and rotateR (m: 'a Node FingerTree) (pr: 'a Digit): 'a FingerTree =
        match viewR m with
        | EmptyTreeR -> digitToTree pr
        | ConsR (a, m') -> deep pr m' (nodeToDigit a)

    let headLeft ft =
        match ft with
        | Deep (D1 a, _, _) -> a
        | Deep (D2 (a, _), _, _) -> a
        | Deep (D3 (a, _, _), _, _) -> a
        | Deep (D4 (a, _, _, _), _, _) -> a
        | Single a -> a
        | Empty -> failwith "Empty Tree"

    let tailLeft ft =
        match viewL ft with
        | ConsL (_, xs) -> xs
        | EmptyTreeL -> failwith "Empty Tree"

    let headRight ft =
        match ft with
        | Deep (_, _, D1 a) -> a
        | Deep (_, _, D2 (_, a)) -> a
        | Deep (_, _, D3 (_, _, a)) -> a
        | Deep (_, _, D4 (_, _, _, a)) -> a
        | Single a -> a
        | Empty -> failwith "Empty Tree"

    let tailRight ft =
        match viewR ft with
        | ConsR (_, xs) -> xs
        | EmptyTreeR -> failwith "Empty Tree"
    
    let rec toSeqLeft<'a> (ft: 'a FingerTree): 'a seq = seq {
       match viewL ft with 
       | EmptyTreeL -> ()
       | ConsL (a, ft') ->
           yield a
           yield! (toSeqLeft ft')
       }

    let rec toSeqRight<'a> (ft: FingerTree<'a>): seq<'a> = seq {
       match viewR ft with 
       | EmptyTreeR -> ()
       | ConsR (a, ft') ->
           yield a
           yield! (toSeqRight ft')
       }

    let fromList ls = List.fold (fun ft a -> addRight a ft) Empty ls

    let fromArray ar = Array.fold (fun ft a -> addRight a ft) Empty ar

    let fromSeq sq = Seq.fold (fun ft a -> addRight a ft) Empty sq
    
    let rec addDigits1<'a> (m0: 'a Node FingerTree) (sf: 'a Digit) (x: 'a) (pr: 'a Digit) (m1: 'a Node FingerTree): 'a Node FingerTree =
        match (sf, x, pr) with
        | (D1 a, b, D1 c)                       -> appendTree1 m0 (node3 a b c) m1
        | (D1 a, b, D2 (c, d))                  -> appendTree2 m0 (node2 a b) (node2 c d) m1
        | (D1 a, b, D3 (c, d, e))               -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D1 a, b, D4 (c, d, e, f))            -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D2 (a, b), c, D1 d)                  -> appendTree2 m0 (node2 a b) (node2 c d) m1
        | (D2 (a, b), c, D2 (d, e))             -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D2 (a, b), c, D3 (d, e, f))          -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D2 (a, b), c, D4 (d, e, f, g))       -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D3 (a, b, c), d, D1 e)               -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D3 (a, b, c), d, D2 (e, f))          -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D3 (a, b, c), d, D3 (e, f, g))       -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D3 (a, b, c), d, D4 (e, f, g, h))    -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D4 (a, b, c, d), e, D1 f)            -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D4 (a, b, c, d), e, D2 (f, g))       -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D4 (a, b, c, d), e, D3 (f, g, h))    -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D4 (a, b, c, d), e, D4 (f, g, h, i)) -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1

    and appendTree1 m0 a m1 =
        match (m0, m1) with
        | (Empty, _)    -> addLeft a m1
        | (_, Empty)    -> addRight a m0
        | (Single b, _) -> addLeft b (addLeft a m1)
        | (_, Single b) -> addRight b (addRight a m0)
        | (Deep (pr0, ft0, sf0), Deep (pr1, ft1, sf1)) -> deep pr0 (addDigits1 ft0 sf0 a pr1 ft1) sf1

    and addDigits2 (m0: 'a Node FingerTree) (sf: 'a Digit) (x0: 'a) (x1: 'a) (pr: 'a Digit) (m1: 'a Node FingerTree): 'a Node FingerTree =
        match (sf, x0, x1, pr) with
        | (D1 a, b, c, D1 d)                       -> appendTree2 m0 (node2 a b) (node2 c d) m1
        | (D1 a, b, c, D2 (d, e))                  -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D1 a, b, c, D3 (d, e, f))               -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D1 a, b, c, D4 (d, e, f, g))            -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D2 (a, b), c, d, D1 e)                  -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D2 (a, b), c, d, D2 (e, f))             -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D2 (a, b), c, d, D3 (e, f, g))          -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D2 (a, b), c, d, D4 (e, f, g, h))       -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D3 (a, b, c), d, e, D1 f)               -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D3 (a, b, c), d, e, D2 (f, g))          -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D3 (a, b, c), d, e, D3 (f, g, h))       -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D3 (a, b, c), d, e, D4 (f, g, h, i))    -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D4 (a, b, c, d), e, f, D1 g)            -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D4 (a, b, c, d), e, f, D2 (g, h))       -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D4 (a, b, c, d), e, f, D3 (g, h, i))    -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D4 (a, b, c, d), e, f, D4 (g, h, i, j)) -> appendTree4 m0 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m1

    and appendTree2<'a> (m0: 'a FingerTree) (a: 'a) (b: 'a) (m1: 'a FingerTree): 'a FingerTree =
        match (m0, m1) with
        | (Empty, _)    -> addLeft a (addLeft b m1)
        | (_, Empty)    -> addRight b (addRight a m0)
        | (Single c, _) -> addLeft c (addLeft a (addLeft b m1))
        | (_, Single c) -> addRight c (addRight b (addRight a m0))
        | (Deep (pr0, ft0, sf0), Deep (pr1, ft1, sf1)) -> deep pr0 (addDigits2 ft0 sf0 a b pr1 ft1) sf1

    and addDigits3 m0 sf x0 x1 x2 pr m1 =
        match (sf, x0, x1, x2, pr) with
        | (D1 a, b, c, d, D1 e)                       -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D1 a, b, c, d, D2 (e, f))                  -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D1 a, b, c, d, D3 (e, f, g))               -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D1 a, b, c, d, D4 (e, f, g, h))            -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D2 (a, b), c, d, e, D1 f)                  -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D2 (a, b), c, d, e, D2 (f, g))             -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D2 (a, b), c, d, e, D3 (f, g, h))          -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D2 (a, b), c, d, e, D4 (f, g, h, i))       -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D3 (a, b, c), d, e, f, D1 g)               -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D3 (a, b, c), d, e, f, D2 (g, h))          -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D3 (a, b, c), d, e, f, D3 (g, h, i))       -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D3 (a, b, c), d, e, f, D4 (g, h, i, j))    -> appendTree4 m0 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m1
        | (D4 (a, b, c, d), e, f, g, D1 h)            -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D4 (a, b, c, d), e, f, g, D2 (h, i))       -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D4 (a, b, c, d), e, f, g, D3 (h, i, j))    -> appendTree4 m0 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m1
        | (D4 (a, b, c, d), e, f, g, D4 (h, i, j, k)) -> appendTree4 m0 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m1

    and appendTree3<'a> (m0: 'a FingerTree) (a: 'a) (b: 'a) (c: 'a) (m1: 'a FingerTree): 'a FingerTree =
        match (m0, m1) with
        | (Empty, _)    -> addLeft a (addLeft b (addLeft c m1))
        | (_, Empty)    -> addRight c (addRight b (addRight a m0))
        | (Single d, _) -> addLeft d (addLeft a (addLeft b (addLeft c m1)))
        | (_, Single d) -> addRight d (addRight c (addRight b (addRight a m0)))
        | (Deep (pr0, ft0, sf0), Deep (pr1, ft1, sf1)) ->  deep pr0 (addDigits3 ft0 sf0 a b c pr1 ft1) sf1

    and addDigits4 m0 sf x0 x1 x2 x3 pr m1 =
        match (sf, x0, x1, x2, x3, pr) with
        | (D1 a, b, c, d, e, D1 f)                       -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D1 a, b, c, d, e, D2 (f, g))                  -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D1 a, b, c, d, e, D3 (f, g, h))               -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D1 a, b, c, d, e, D4 (f, g, h, i))            -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D2 (a, b), c, d, e, f, D1 g)                  -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D2 (a, b), c, d, e, f, D2 (g, h))             -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D2 (a, b), c, d, e, f, D3 (g, h, i))          -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D2 (a, b), c, d, e, f, D4 (g, h, i, j))       -> appendTree4 m0 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m1
        | (D3 (a, b, c), d, e, f, g, D1 h)               -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1
        | (D3 (a, b, c), d, e, f, g, D2 (h, i))          -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D3 (a, b, c), d, e, f, g, D3 (h, i, j))       -> appendTree4 m0 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m1
        | (D3 (a, b, c), d, e, f, g, D4 (h, i, j, k))    -> appendTree4 m0 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m1
        | (D4 (a, b, c, d), e, f, g, h, D1 i)            -> appendTree3 m0 (node3 a b c) (node3 d e f) (node3 g h i) m1
        | (D4 (a, b, c, d), e, f, g, h, D2 (i, j))       -> appendTree4 m0 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m1
        | (D4 (a, b, c, d), e, f, g, h, D3 (i, j, k))    -> appendTree4 m0 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m1
        | (D4 (a, b, c, d), e, f, g, h, D4 (i, j, k, l)) -> appendTree4 m0 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m1

    and appendTree4<'a> (m0: 'a FingerTree) (a: 'a) (b: 'a) (c: 'a) (d: 'a) (m1: 'a FingerTree): 'a FingerTree =
        match (m0, m1) with
        | (Empty, _)    -> addLeft a (addLeft b (addLeft c (addLeft d m1)))
        | (_, Empty)    -> addRight d (addRight c (addRight b (addRight a m0)))
        | (Single e, _) -> addLeft e (addLeft a (addLeft b (addLeft c (addLeft d m1))))
        | (_, Single e) -> addRight e (addRight d (addRight c (addRight b (addRight a m0))))
        | (Deep (pr0, ft0, sf0), Deep (pr1, ft1, sf1)) ->  deep pr0 (addDigits4 ft0 sf0 a b c d pr1 ft1) sf1

    let addDigits0 (m0: 'a Node FingerTree) (sf: 'a Digit) (pr: 'a Digit) (m1: 'a Node FingerTree): 'a Node FingerTree =
        match (sf, pr) with
        | (D1 a, D1 b)                       -> appendTree1 m0 (node2 a b) m1
        | (D1 a, D2 (b, c))                  -> appendTree1 m0 (node3 a b c) m1
        | (D1 a, D3 (b, c, d))               -> appendTree2 m0 (node2 a b) (node2 c d) m1
        | (D1 a, D4 (b, c, d, e))            -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D2 (a, b), D1 c)                  -> appendTree1 m0 (node3 a b c) m1
        | (D2 (a, b), D2 (c, d))             -> appendTree2 m0 (node2 a b) (node2 c d) m1
        | (D2 (a, b), D3 (c, d, e))          -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D2 (a, b), D4 (c, d, e, f))       -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D3 (a, b, c), D1 d)               -> appendTree2 m0 (node2 a b) (node2 c d) m1
        | (D3 (a, b, c), D2 (d, e))          -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D3 (a, b, c), D3 (d, e, f))       -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D3 (a, b, c), D4 (d, e, f, g))    -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D4 (a, b, c, d), D1 e)            -> appendTree2 m0 (node3 a b c) (node2 d e) m1
        | (D4 (a, b, c, d), D2 (e, f))       -> appendTree2 m0 (node3 a b c) (node3 d e f) m1
        | (D4 (a, b, c, d), D3 (e, f, g))    -> appendTree3 m0 (node3 a b c) (node2 d e) (node2 f g) m1
        | (D4 (a, b, c, d), D4 (e, f, g, h)) -> appendTree3 m0 (node3 a b c) (node3 d e f) (node2 g h) m1

    let appendTree0 (m0: 'a FingerTree) (m1: 'a FingerTree): 'a FingerTree =
        match (m0, m1) with
        | (Empty, ft1) -> ft1
        | (ft0, Empty) -> ft0
        | (Single a, ft1) -> addLeft a ft1
        | (ft0, Single a) -> addRight a ft0
        | (Deep (pr0, m0, sf0), Deep (pr1, m1, sf1)) -> deep pr0 (addDigits0 m0 sf0 pr1 m1) sf1

    let append = appendTree0
