fun inc x = x + 1;

let
    val x = fn n => n + 2
in
    x 3
end;

fun fact n =  
let
    val r = ref inc
    val f = fn n => if n = 1 then 1 else n * ((!r)(n - 1))
in
    r := f;
    f n
end;

(*Alternatively*)
let 
    val r = ref (fn n => n + 1)
in
    let
        val f = fn n => if n = 1 then 1 else n * ((!r)(n - 1))
    in
        r := f;
        f 
    end
end;

let
    val r = ref inc
    val f = fn n => (!r)n
in
    r := f;
    f 
end;


fact = λ.n : Nat.
    let 
        r = ref (λx : Nat.x + 1)
    in
        let
            f = λn : Nat.if n <= 1 then 1 else n * ((!r)(n - 1))
        in
            r := f;
            f n


endless = λ.n : Nat.
    let 
        r = ref (λx : Nat.x + 1)
    in
        let
            f = λn : Nat.(!r)n
        in
            r := f;
            f n