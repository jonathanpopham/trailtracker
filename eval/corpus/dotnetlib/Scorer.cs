using System;
using System.Collections.Generic;

namespace DotNetLib
{
    /// <summary>Scores integer samples. The CPG fixture class:
    /// Score's control-flow graph is hand-verified in
    /// src/lang/csharp/cpg.rs (hand_verified_cfg_for_score).</summary>
    public class Scorer
    {
        private readonly int _floor;

        public Scorer(int floor)
        {
            _floor = floor;
        }

        public int Score(int[] xs)
        {
            int total = 0;
            foreach (var x in xs)
            {
                if (x < 0) { continue; }
                total += x;
            }
            switch (total)
            {
                case 0: return -1;
                default: break;
            }
            return total;
        }

        public int Clamp(int value)
        {
            if (value < _floor)
            {
                return _floor;
            }
            return value;
        }
    }
}
