// Learn more about F# at http://fsharp.org

open System
open FingerTrees

[<EntryPoint>]
let main argv =
    let N = 20
    
    let ft =
        Seq.fold
            (fun s x ->
                let t = FingerTrees.addLeft x s
                printfn "%d: %A" x t
                t)
            FingerTrees.Empty
            { 1 .. N }
    
    Console.WriteLine("Press any key")
    Console.ReadLine() |> ignore

    0 // return an integer exit code
