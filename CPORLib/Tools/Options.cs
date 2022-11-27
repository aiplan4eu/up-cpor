
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text;
using System.Threading;

namespace CPORLib.Tools
{
    public class Options
    {
        public enum DeadEndExistence { DeadEndFalse = 0, DeadEndTrue = 1, MaybeDeadEnd = 2 };
        public enum DeadendStrategies { Active, Lazy, Both, Classical };

        public static DeadendStrategies DeadendStrategy = DeadendStrategies.Lazy;

        public static bool UseOptions = true;
        public static bool ReplaceNonDeterministicEffectsWithOptions = true;
        public static bool UseCosts { get; private set; }


        public static bool SampleDeadendState = true;

        public static bool RemoveConflictingConditionalEffects = false;

        public static bool SDR_OBS { set; get; }

        public enum Translations { SDR, MPSRTagPartitions, MPSRTags, BestCase, Conformant, SingleStateK }
        public enum Planners { FFCS, LocalFSP }
        public static Planners Planner = Planners.FFCS;
 
        public static bool AllowChoosingNonDeterministicOptions = true;
        private static Dictionary<Thread, Process> FFProcesses = new Dictionary<Thread, Process>();

        public static bool TryImmediatePlan = false;
        public static Translations Translation = Translations.SDR;
        //public static Translations Translation = Translations.SingleStateK;

        public ExecutionData Data { get; private set; }
        // OptimizeMemoryConsumption= true in offline planning 
        //OptimizeMemoryConsumption= false in online planning 
        public static bool OptimizeMemoryConsumption = false;
        // for offline planning use this flag with true
        public static bool ComputeCompletePlanTree = false;
        //  use this flag with false


        //public static bool ComputeCompletePlanTree = false;
        public static TimeSpan PlannerTimeout = new TimeSpan(0, 1, 0);
        public static bool WriteAllKVariations = false;
        public static bool ConsiderStateNegations = false;
        public static bool SplitConditionalEffects = false;
        public static bool RemoveAllKnowledge = true;
        public static bool ForceTagObservations = false;
        public static bool EnforceCNF = false;
        public static bool UseDomainSpecificHeuristics = false;

        public static bool AddAllKnownToGiven { get; set; }
        public static bool AddTagRefutationToGoal { get; set; }

        public static List<string> SimulationStartState { get; set; }
        public static string GivenPlanFile = null;

        public static int TagsCount = 2;

        public const int TIME_STEPS = 0;
        public const int MAX_OPTIONS = 2;


    }
}
