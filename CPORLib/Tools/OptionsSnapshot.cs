using System;
using System.Collections.Generic;

namespace CPORLib.Tools
{
    internal sealed class OptionsSnapshot : IDisposable
    {
        private readonly Options.DeadendStrategies _deadendStrategy = Options.DeadendStrategy;
        private readonly bool _useOptions = Options.UseOptions;
        private readonly bool _replaceNonDeterministicEffectsWithOptions = Options.ReplaceNonDeterministicEffectsWithOptions;
        private readonly bool _sampleDeadendState = Options.SampleDeadendState;
        private readonly bool _removeConflictingConditionalEffects = Options.RemoveConflictingConditionalEffects;
        private readonly bool _sdrObs = Options.SDR_OBS;
        private readonly bool _recursiveClosedStates = Options.RecursiveClosedStates;
        private readonly Options.Planners _planner = Options.Planner;
        private readonly bool _allowChoosingNonDeterministicOptions = Options.AllowChoosingNonDeterministicOptions;
        private readonly bool _tryImmediatePlan = Options.TryImmediatePlan;
        private readonly Options.Translations _translation = Options.Translation;
        private readonly bool _optimizeMemoryConsumption = Options.OptimizeMemoryConsumption;
        private readonly bool _computeCompletePlanTree = Options.ComputeCompletePlanTree;
        private readonly TimeSpan _plannerTimeout = Options.PlannerTimeout;
        private readonly bool _writeAllKVariations = Options.WriteAllKVariations;
        private readonly bool _considerStateNegations = Options.ConsiderStateNegations;
        private readonly bool _splitConditionalEffects = Options.SplitConditionalEffects;
        private readonly bool _removeAllKnowledge = Options.RemoveAllKnowledge;
        private readonly bool _forceTagObservations = Options.ForceTagObservations;
        private readonly bool _enforceCnf = Options.EnforceCNF;
        private readonly bool _useDomainSpecificHeuristics = Options.UseDomainSpecificHeuristics;
        private readonly bool _addAllKnownToGiven = Options.AddAllKnownToGiven;
        private readonly bool _addTagRefutationToGoal = Options.AddTagRefutationToGoal;
        private readonly List<string> _simulationStartState = Options.SimulationStartState == null
            ? null
            : new List<string>(Options.SimulationStartState);
        private readonly string _givenPlanFile = Options.GivenPlanFile;
        private readonly int _tagsCount = Options.TagsCount;
        private bool _disposed;

        public void Dispose()
        {
            if (_disposed)
            {
                return;
            }

            Options.DeadendStrategy = _deadendStrategy;
            Options.UseOptions = _useOptions;
            Options.ReplaceNonDeterministicEffectsWithOptions = _replaceNonDeterministicEffectsWithOptions;
            Options.SampleDeadendState = _sampleDeadendState;
            Options.RemoveConflictingConditionalEffects = _removeConflictingConditionalEffects;
            Options.SDR_OBS = _sdrObs;
            Options.RecursiveClosedStates = _recursiveClosedStates;
            Options.Planner = _planner;
            Options.AllowChoosingNonDeterministicOptions = _allowChoosingNonDeterministicOptions;
            Options.TryImmediatePlan = _tryImmediatePlan;
            Options.Translation = _translation;
            Options.OptimizeMemoryConsumption = _optimizeMemoryConsumption;
            Options.ComputeCompletePlanTree = _computeCompletePlanTree;
            Options.PlannerTimeout = _plannerTimeout;
            Options.WriteAllKVariations = _writeAllKVariations;
            Options.ConsiderStateNegations = _considerStateNegations;
            Options.SplitConditionalEffects = _splitConditionalEffects;
            Options.RemoveAllKnowledge = _removeAllKnowledge;
            Options.ForceTagObservations = _forceTagObservations;
            Options.EnforceCNF = _enforceCnf;
            Options.UseDomainSpecificHeuristics = _useDomainSpecificHeuristics;
            Options.AddAllKnownToGiven = _addAllKnownToGiven;
            Options.AddTagRefutationToGoal = _addTagRefutationToGoal;
            Options.SimulationStartState = _simulationStartState == null
                ? null
                : new List<string>(_simulationStartState);
            Options.GivenPlanFile = _givenPlanFile;
            Options.TagsCount = _tagsCount;
            _disposed = true;
        }
    }
}
