Sirkel is a DHT based on Chord

To use, compile Main.hs with `ghc -threaded --make Main.hs`

afterwards run as many Sirkel instances you want on the network you have.
It only supports LAN or boxes directly connected to the internet yet.

to put data into the DHT write "put " preceded by the data and press enter.

example:
    put abc123

The data will the be saved in the DHT.
All nodes can now "get" the data using the SHA-1 hash of the data.

When you write the `put` the output will be a list of keys. These keys are the SHA-1
hashes of the blocks that your data was chunked intoo before it was put.

to get some data back, just write `get [key1, key2, key3]`
where `key1 ... key3` are the keys that where output from the `put`.
Note that to get your data correctly the order of the keys in the get
matters. Each key represents a block of data. First each of them are retrieved from
the DHT, then they are concatenated together to form the final data. If you mess up the order,
the concatenation will be messed up and therefore also the deserialization.

In Main.hs there is a initState. The fields in this state determines how your DHT works.

    initState = NodeState {
          self = undefined
        , fingerTable = Map.empty -- ^ The fingerTable
        , blockDir = "/tmp/"
        , predecessor = undefined
        , timeout = 10 -- ^ The timout latency of ping
        , m = 160 -- ^ The number of bits in a key, ususaly 160
        , r = 5 -- ^ the number of successors
        , b = 2 -- ^ the nuber of replicas
        , blockSize = 10 -- ^ the number of bytes a block is
        }

`self` is a reference to ourselves and should be left undefined, it is populated when you initialize the DHT.
`fingerTable` is our "address book". It tells us whom to ask what, and also who most likely to know what.
`blockDir` is currently not used since blocks are stored in RAM
`predecessor` is a reference to our predecessor in the Chord ring. It should be left empty for the same reason as self.
`timeout` is not used yet but will be used to determine how long to way for a reply from the DHT.
`m` is the number of bits that makes up the keyspace of the Chord ring. Note that it can not be changed without changing the hashing algorithm which is not supported yet.
`r` is one of the most important parameters. It determines how many immediate successors you keep. This has consequences that we'll look on soon.
`b` is the number of replicas of each block that should be kept, the node responsible for a block will make shure that its `b` successors has a copy of it's blocks so that in the event of node failure they can take over the role as owners of the block.
`blockSize` is the numbers of bytes a block should have. When you try to put data, it will first be chunked into blocks of this size, then each block will be hashed and put separately.

Now, more on the `r` number. Each node keeps `r` successors.
That means that if we are asked for the successor of a key that preceeds
our `r`th successor we know that our `r`th successor is the successor of
that key. We do not know anything about `r`s successors though, because
we only keep a list of the first `r` of us and the `r`th successor is the
last in that list. Therefore, in all calls that "get" something, `findSuccessors`,
`getBlock` and `getObject`, there is a `howMany` argument. This specifies how
many successors we need back. At most we can get `r` successors back since no node
keeps a list of more than that. But say if we only need the first successor of a key.
Then we call `findSuccessors` with `howMany = 1` which lets not just the immediate predecessor
of the key answer our call, but all the predecessors that have at-least one successor to that key.
This boils down to that the `r` nodes before the key can answer. Therefore the argument `howMany`
lets you specify how "exact" your query is. If you choose `howMany = r` then only one node in the
ring can answer that query. For `howMany <= r`, `r + 1 - howMany` nodes can answer your query.
This means that if you don't need that detailed information about the successors of a key, maybe
just the first one, the reliability and speed of your query increases.

This is especially important for small networks. If the `r` parameter is larger than the number
of Sirkel nodes then all nodes know all others and there will be no network traffic to resolve
a query. This off-course comes to a price. You have to store the contact information about `r`
nodes so for a million nodes network `r` must be kept at a reasonable level.

For questions, send me an e-mail at morten@lysgaard.no
[Projects webpage](mortenlysgaard.com)
[Projects Github page](https://github.com/molysgaard/Sirkel)
