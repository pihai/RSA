// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.

open System
open System.Numerics

let random = Random()

// this is a modulo function which can handle the negative case correctly
let inline modulo n m =
  let mod' = n % m
  if sign mod' >= 0 then mod'
  else abs m + mod'

let rec randomNumber (minInclusive : bigint) (maxInclusive : bigint) =
  let bytes = (maxInclusive - minInclusive).ToByteArray()
  random.NextBytes bytes
  bytes.[bytes.Length-1] <- bytes.[bytes.Length-1] &&& 127uy // force to be positive, through settinng the sign bit to 0
  let nr = BigInteger(bytes) + minInclusive
  if nr <= maxInclusive then nr else randomNumber minInclusive maxInclusive // generate a new value until the random number fits into the desired range

let powMod a m n = // a^m (mod n)
  let rec calc M y z =
    if M % 2I = 0I then
      calc (M/2I) y ((z*z) % n)
    else
      if (M/2I) = 0I then (z*y)%n
      else calc (M/2I) ((z*y)%n) ((z*z) % n)
  calc m 1I a
  
let millerRabinPrimeTest n k =
  let d,s =
    let rec factor s d =
      if d % 2I = 1I then d,s
      else factor (s+1I) (d/2I)
    factor 0I (n-1I)

  let rec witnessLoop iteration =
    if iteration < k then
      let a = randomNumber 2I (n-2I)
      let x = powMod a d n
      if x = 1I || x = n - 1I then
        witnessLoop (iteration + 1)
      else
        let isComposite =
          ((seq { 1I .. s - 1I }
          |> Seq.scan (fun x' _ -> powMod x' 2I n) x
          |> Seq.tryPick (fun x' -> if   x' = 1I     then Some true
                                    elif x' = n - 1I then Some false
                                    else None))
          |> defaultArg) true
        if isComposite then false else witnessLoop (iteration+1)
    else
      true
  if n % 2I <> 0I then witnessLoop 0 else false
  
let randomPrimes bits =
  seq {
    while true do
      let number = randomNumber (pown 2I (bits-1)) (pown 2I bits)
      if millerRabinPrimeTest number 100 then yield number 
  }

let randomPrime bits = randomPrimes bits |> Seq.head
let between min max x = x > min && x < max

let rec gcd a b =
  let r = a % b
  if r = 0I then b else gcd b r

let gcdExtended n k =
  let rec loop (ni, n2, n3) (ri, ui, vi) =
    let q, r = BigInteger.DivRem(ni, ri)
    if r = 0I then ri, ui, vi
    else
      let R = ni - q * ri, n2 - q * ui, n3 - q * vi
      loop (ri, ui, vi) R
  loop (n, 1I, 0I) (k, 0I, 1I)

let generateKey bits =
  // chose p,q such that p and q are different and 0.1 <= |log2(p) - log2(q)| < 30
  let p,q =
    Seq.zip (randomPrimes bits) (randomPrimes bits)
    |> Seq.filter (fun (p,q) -> p <> q)
    |> Seq.filter (fun (p,q) -> abs ((BigInteger.Log p) - BigInteger.Log q) |> between 0.1 30.0)
    |> Seq.head
  let n = p * q
  let phi = (p-1I) * (q-1I)
  // choose a random number e such that 1 < e < phi(n) and e is relative prime to phi(n) (gcd(e, phi(n) = 1)
  let e = Seq.initInfinite (fun _ -> randomNumber 2I (phi - 1I)) |> Seq.filter (fun e -> (gcd phi e) = 1I) |> Seq.head
  // calculate d as the inverse of e mod phi(n) such that e * d = 1 (mod n)
  let _,_,d = gcdExtended phi e
  n, e, (modulo d phi) // d is negative in many cases, therefore use the default representative

[<EntryPoint>]
let main argv = 
    let n, e, d = generateKey 1024

    let m = 42I
    let c = powMod m e n
    let m' = powMod c d n

    printfn "n = %A" n
    printfn "e = %A" e
    printfn "d = %A" d

    printfn "c = %A" c
    printfn "m': %A" m'

    Console.Read() |> ignore

    printfn "%A" argv
    0 // return an integer exit code
