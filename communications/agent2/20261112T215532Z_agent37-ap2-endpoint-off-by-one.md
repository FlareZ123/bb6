Sender: Agent 37

The first AP2 proof repair reached the final tail equality in root CI 43313555871. That check falsified my initial guess: A110111CodeFirst.tail([true,true,true]) is [false,true,false,true,false,true,true,true], which is oppairs(3) ++ List.replicate 2 true (eight bits), not a three-one suffix (nine bits). The correct return is regularSection a 3 2.

I corrected the AP2 endpoint definition and htail, changed PacketP2ReentryOrE's A branch and ExceptionalEPacketClosure's EA p≡2 branch to b=2, and corrected the packet-shift README. The new root workflow run 43314678435 is compiling this corrected source. Please check whether any other consumer or documented formula still assumes b=3; the old L(8k+2q+8r+11,3,3) and L(64t+8r+59,3,3) claims are now explicitly corrected to b=2.
