# Protocol overview

We simplify the Proof-of-Stake (PoS) Ethereum protocol:

Time is divided in slots of 12 seconds.

A block proposer is expected to send their block B

at t=0
seconds into the first slot.
At t=4
seconds into the slot, an attester is expected to publish their view of the chain v: the hash of B if it is available, or an empty vote ∅
otherwise.
At t=12
seconds into the slot (i.e., t=0 into the next slot), the game is repeated: a block proposer is expected to send a block B′, which contains v if v
was received in time by the proposer.
The attester is rewarded if their vote is included in block B′
and is correct, i.e., voted ∅ if B′ did not build on B, and hash(B)

    otherwise.

NOTE: That seems to be a critical assumption. With two players, how can we actually confirm the state of the world? More generally, is the state of the world what the attesters decide? Or is there some additional source of truth?


Propagation times follow some distribution F
: with probability F(t), a message sent is received after delay t. Although the protocol dictates sending the vote after 4 seconds, there is a weak incentive to wait a little longer in case B is delayed for some reason and is received in time for B′ to build on it, albeit too late for attesters who voted at t=4 to have seen it.


# Multiplayer

The rules remain pretty much the same, but now we have multiple attesters at each round. We have a tree of blocks and we consider the head block to be the leaf that has accumulated the most attestations, according to the GHOST rule.

    GHOST rule: Start from the root and find the weight of each block by recursively going through each child and counting the number of votes downstream. The canonical chain starts from the root and at each fork chooses the block with the highest weight. The head of the chain is the first encountered leaf.

    Attesters from slot n

are expected to vote for the head of the chain at that slot. They may believe the head of the chain is h(n−1) if they don’t receive h(n) in time, but later on, if h(n) becomes part of the canonical chain, these attesters would be given 0

    .
    A weight-giving vote is a head vote from any attester.

## Proposed model

There are two stages, two block proposers and four attesters in total, two per block. A root block h(0)

is given.

    The first block proposer is expected to propose on the root block, h↑(1)=h(0)

.
a. If the first two attesters (A & B) see the block, they should vote on h(1), otherwise h(0)
.
The second proposer may propose either on h(0)
or h(1)

NOTE: Does this mean, the 2nd proposer sees the initial block? How can he otherwise choose?

    .
    b. The next two attesters (C & D) vote on the block they believe to be the head.

We either have:

a. a linear graph h(0)↓h(1)↓h(2)

, or

b. a fork (h(0)↓h(1))&(h(0)↓h(2))

.

In the case of a linear graph, if attesters A & B voted on h(1)
, they receive r. If C & D voted on h(2), they receive r. If either of the attesters didn’t vote on the correct block, they receive 0

(A and B could have different behaviours).

In the case of a fork, the head is either h(1)
or h(2). This is determined by the GHOST rule. For instance, if A votes h(0), C and D vote h(2), then h(2) will be the head, and A, C and D would be rewarded, while both proposer B(1) and attester B would get 0.
