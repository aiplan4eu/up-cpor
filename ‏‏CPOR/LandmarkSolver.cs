using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;

namespace CPOR
{
    class LandmarkSolver
    {

        public void IdentifyLandmarks(Problem p, Domain d)
        {
            //State s0 = p.GetInitialBelief().ChooseState(true);
            Debug.WriteLine("Started identifying landmarks");
            HashSet<Predicate> lInitialState = new HashSet<Predicate>(p.Known);
            lInitialState = CompleteNegations(lInitialState, d);
            List<Formula> lLandmarks = new List<Formula>();
            Queue<Formula> qOpenLandmarks = new Queue<Formula>();
            Debug.WriteLine("Grounding actions");
            List<Action> lGrounded = d.GroundAllActions(p, true);
            Debug.WriteLine("Removing disjunctions, conditional effects, and filtering impossible actions");
            List<Action> lNoDisjunctions = RemoveDisjunctions(lGrounded);//remove disjunctions before grounding?
            List<Action> lSimple = RemoveConditions(lNoDisjunctions);
            lSimple = FilterImpossible(lSimple, lInitialState, d);
            //lSimple = RemoveNegativePreconditions(lSimple);//need to remove this! enables many illegal actions - must work with complete positive and negative specification
            Dictionary<Predicate, List<Action>> dPreconditionToAction = new Dictionary<Predicate, List<Action>>();
            Dictionary<Predicate, List<Action>> dEffectToAction = new Dictionary<Predicate, List<Action>>();
            ClassifyActions(lSimple, dPreconditionToAction, dEffectToAction);
            Debug.WriteLine("Processing landmarks");
            foreach (Predicate pLandmark in p.Goal.GetAllPredicates())
            {
                lLandmarks.Add(new PredicateFormula(pLandmark));
                qOpenLandmarks.Enqueue(new PredicateFormula(pLandmark));
            }
            Dictionary<Predicate, List<Formula>> dLandmarksForPredicate = new Dictionary<Predicate, List<Formula>>();
            int cProcessed = 0;
            while (qOpenLandmarks.Count > 0)
            {
                Formula fCurrent = qOpenLandmarks.Dequeue();
                List<Action> lFiltered = new List<Action>(), lPotentialLandmarkAchievers = new List<Action>();
                FilterActions(lSimple, fCurrent, lFiltered, lPotentialLandmarkAchievers, dPreconditionToAction, dEffectToAction, lInitialState);
                HashSet<Predicate> lAllReachable = ReachablePredicates(lInitialState, lFiltered);
                Dictionary<Predicate, List<Action>> dLandmarkAchievers = GetLandmarkAchievers(fCurrent, lAllReachable, lPotentialLandmarkAchievers);
                List<Formula> lNewLandmarks = RegressLandmark(fCurrent, dLandmarkAchievers, lInitialState);
                foreach (Formula fNew in lNewLandmarks)
                {
                    bool bAlreadyFound = false;
                    foreach (Predicate pLandmark in fNew.GetAllPredicates())
                    {
                        if (!dLandmarksForPredicate.ContainsKey(pLandmark))
                            dLandmarksForPredicate[pLandmark] = new List<Formula>();
                        else
                        {
                            foreach (Formula fExisting in dLandmarksForPredicate[pLandmark])
                            {
                                if (fExisting.Size <= fNew.Size)
                                    bAlreadyFound = true;
                            }
                        }
                        dLandmarksForPredicate[pLandmark].Add(fNew);
                    }
                    if (!bAlreadyFound)
                    {
                        qOpenLandmarks.Enqueue(fNew);
                        lLandmarks.Add(fNew);
                    }
                }
                cProcessed++;
                if (cProcessed % 10 == 0)
                    Debug.WriteLine("Processed " + cProcessed + " found " + lLandmarks.Count + " in queue " + qOpenLandmarks.Count);
            }
            StreamWriter sw = new StreamWriter("D:\\" + d.Name + ".Landmarks.txt");
            foreach (Formula f in lLandmarks)
                sw.WriteLine(f);
            sw.Close();

        }

        private HashSet<Predicate> CompleteNegations(HashSet<Predicate> lPartial, Domain d)
        {
            HashSet<Predicate> lAll = new HashSet<Predicate>(lPartial);
            HashSet<GroundedPredicate> lGrounded = d.GroundAllPredicates();
            foreach (GroundedPredicate gp in lGrounded)
            {
                if (!lPartial.Contains(gp))
                    lAll.Add(gp.Negate());
            }
            return lAll;

        }

        private List<Action> RemoveNegativePreconditions(List<Action> lActions)
        {
            List<Action> lDeleteRelaxation = new List<Action>();
            foreach (Action a in lActions)
            {
                Action aDeleteRelaxation = a.Clone();
                aDeleteRelaxation.Preconditions = a.Preconditions.RemoveNegations();
                lDeleteRelaxation.Add(aDeleteRelaxation);
            }
            return lDeleteRelaxation;
        }

        private List<Action> FilterImpossible(List<Action> lActions, HashSet<Predicate> lInitialState, Domain d)
        {
            List<Action> lPossible = new List<Action>();
            List<Action> lImpossible = new List<Action>();
            foreach (Action a in lActions)
            {
                bool bPossible = true;
                HashSet<Predicate> lPreconditions = a.Preconditions.GetAllPredicates();
                foreach (Predicate p in lPreconditions)
                {
                    if (d.AlwaysConstant(p)) //we can remove them from the preconditions
                    {

                        if ((p.Negation && lInitialState.Contains(p.Negate())) || (!p.Negation && !lInitialState.Contains(p)))
                        {
                            bPossible = false;
                            break;
                        }

                    }
                }
                if (bPossible)
                    lPossible.Add(a);
                else
                    lImpossible.Add(a);
            }
            return lPossible;
        }

        private void ClassifyActions(List<Action> lSimple, Dictionary<Predicate, List<Action>> dPreconditionToAction, Dictionary<Predicate, List<Action>> dEffectToAction)
        {
            foreach (Action a in lSimple)
            {
                HashSet<Predicate> lPre = a.Preconditions.GetAllPredicates();
                foreach (Predicate p in lPre)
                {
                    if (!dPreconditionToAction.ContainsKey(p))
                        dPreconditionToAction[p] = new List<Action>();
                    dPreconditionToAction[p].Add(a);
                }

                HashSet<Predicate> lEffects = a.Effects.GetAllPredicates();
                foreach (Predicate p in lEffects)
                {
                    if (!dEffectToAction.ContainsKey(p))
                        dEffectToAction[p] = new List<Action>();
                    dEffectToAction[p].Add(a);
                }

            }
        }

        private List<Action> RemoveConditions(List<Action> lActions)
        {
            List<Action> lNoConditions = new List<Action>();
            foreach (Action a in lActions)
            {
                HashSet<Predicate> lMandatory = a.GetMandatoryEffects();
                List<CompoundFormula> lConditions = a.GetConditions();
                if (lConditions.Count == 0)
                {
                    lNoConditions.Add(a);
                }
                else
                {
                    int iCondition = 0;
                    foreach (CompoundFormula cfCondition in lConditions)
                    {
                        Action aNew = new Action(a.Name + "." + iCondition);
                        CompoundFormula cfPreconditions = new CompoundFormula("and");
                        cfPreconditions.AddOperand(a.Preconditions);
                        cfPreconditions.AddOperand(cfCondition.Operands[0]);
                        if (!cfPreconditions.IsFalse(null))
                        {
                            aNew.Preconditions = cfPreconditions;
                            CompoundFormula cfEffects = new CompoundFormula("and");
                            cfEffects.AddOperand(cfCondition.Operands[1]);
                            foreach (Predicate p in lMandatory)
                                cfEffects.AddOperand(p);
                            aNew.Effects = cfEffects;
                            lNoConditions.Add(aNew);
                            iCondition++;
                        }
                    }
                }
            }
            return lNoConditions;
        }

        private List<Action> RemoveDisjunctions(List<Action> lGrounded)
        {
            List<Action> lNoDisjunctions = new List<Action>();
            foreach (Action a in lGrounded)
            {
                //if (a.Name.Contains("move-KW-tag0"))
                //      Debug.WriteLine("*");
                if (a.Preconditions == null || a.Preconditions is PredicateFormula)
                    lNoDisjunctions.Add(a);
                else
                {
                    HashSet<Predicate> hsMandatory = new HashSet<Predicate>();
                    List<List<Formula>> lOptions = new List<List<Formula>>();
                    ((CompoundFormula)a.Preconditions).IdentifyDisjunctions(lOptions, hsMandatory);
                    CompoundFormula cfAnd = new CompoundFormula("and");
                    foreach (Predicate p in hsMandatory)
                        cfAnd.AddOperand(p);
                    int iIndex = 0;
                    RemoveDisjunctions(a, lOptions, 0, cfAnd, lNoDisjunctions, ref iIndex);
                }
            }
            return lNoDisjunctions;
        }

        private void RemoveDisjunctions(Action a, List<List<Formula>> lOptions, int iOption, CompoundFormula cfAnd, List<Action> lNoDisjunctions, ref int iIndex)
        {
            if (iOption == lOptions.Count)
            {
                Action aNew = a.Clone();
                aNew.Name += "." + iIndex;
                iIndex++;
                aNew.Preconditions = cfAnd;
                lNoDisjunctions.Add(aNew);
            }
            else
            {
                foreach (Formula fOption in lOptions[iOption])
                {
                    CompoundFormula cfNew = (CompoundFormula)cfAnd.Clone();
                    cfNew.AddOperand(fOption);
                    RemoveDisjunctions(a, lOptions, iOption + 1, cfNew, lNoDisjunctions, ref iIndex);
                }
            }
        }

        private HashSet<Predicate> GetJointPreconditions(List<Action> lActions)
        {
            HashSet<Predicate> lJointPreconditions = null;
            foreach (Action a in lActions)
            {
                HashSet<Predicate> lActionPreconditions = a.Preconditions.GetAllPredicates();
                if (lJointPreconditions == null)
                    lJointPreconditions = lActionPreconditions;
                else
                {
                    lJointPreconditions.IntersectWith(lActionPreconditions);
                }
            }
            return lJointPreconditions;
        }

        private Dictionary<string, Dictionary<string, List<Predicate>>> GetDisjunctivePreconditions(List<Action> lActions, HashSet<Predicate> lInitialState)
        {
            Dictionary<string, Dictionary<string, List<Predicate>>> dDisjunctions = new Dictionary<string, Dictionary<string, List<Predicate>>>();
            foreach (Action a in lActions)
            {
                HashSet<Predicate> lActionPreconditions = a.Preconditions.GetAllPredicates();
                foreach (GroundedPredicate pPrecondition in lActionPreconditions)
                {
                    if (!lInitialState.Contains(pPrecondition))
                    {
                        string sPreconditionName = pPrecondition.Name;
                        if (sPreconditionName.StartsWith("Given"))
                            sPreconditionName = sPreconditionName + "." + pPrecondition.Constants.Last().Name;
                        if (!dDisjunctions.ContainsKey(sPreconditionName))
                        {
                            dDisjunctions[sPreconditionName] = new Dictionary<string, List<Predicate>>();
                        }
                        if (!dDisjunctions[sPreconditionName].ContainsKey(a.Name))
                        {
                            dDisjunctions[sPreconditionName][a.Name] = new List<Predicate>();
                        }
                        dDisjunctions[sPreconditionName][a.Name].Add(pPrecondition);
                    }
                }
            }
            return dDisjunctions;
        }
        /*
                private List<Formula> GetLandmarks(Formula fCurrentLandmark, Dictionary<Predicate, List<Action>> dLandmarkAchievers, HashSet<Predicate> lInitialState)
                {
                    CompoundFormula cfOr = new CompoundFormula("or");
                    List<Formula> lFormulas = new List<Formula>();
                    foreach (Predicate pKey in dLandmarkAchievers.Keys)
                    {
                        List<Action> lActions = dLandmarkAchievers[pKey];
                        if (lActions.Count == 0)
                            continue;
                        //looking for preconditions that are needed for all actions that achieve p
                        HashSet<Predicate> lJointPreconditions = GetJointPreconditions(lActions);
                        bool bNewLandmarkFound = false;
                        if (lJointPreconditions.Count > 0)
                        {
                            CompoundFormula cfAnd = new CompoundFormula("and");
                            foreach (Predicate p in lJointPreconditions)
                            {
                                if (!lInitialState.Contains(p))
                                {
                                    cfAnd.AddOperand(p);
                                    bNewLandmarkFound = true;
                                }
                            }
                            if(bNewLandmarkFound)
                                cfOr.AddOperand(cfAnd);
                        }
                        if(!bNewLandmarkFound)
                        {
                            Dictionary<string, List<Predicate>> dDisjunctions = GetDisjunctivePreconditions(lActions);
                            foreach (List<Predicate> l in dDisjunctions.Values)
                            {
                                if (l.Count >= lActions.Count)
                                {
                                    CompoundFormula cfInternalOr = new CompoundFormula("or");
                                    foreach (Predicate p in l)
                                    {
                                        if (!lInitialState.Contains(p))
                                        {

                                            cfOr.AddOperand(p);
                                        }
                                    }
                                    if (cfInternalOr.Operands.Count > 0)
                                        cfOr.AddOperand(cfInternalOr);
                                }
                            }
                        }
                    }
                    Formula fSimplified = cfOr.Simplify();
                    if (fSimplified is PredicateFormula)
                        lFormulas.Add(fSimplified);
                    else
                    {
                        CompoundFormula cf = (CompoundFormula)fSimplified;
                        if (cf.Operator == "or")
                            lFormulas.Add(cf);
                        else
                        {
                            foreach (Formula fSub in cf.Operands)
                                lFormulas.Add(fSub);
                        }

                    }
                    return lFormulas;
                }
        */


        private bool RegressLandmark(Predicate pCurrentLandmark, List<Action> lLandmarkAchievers, HashSet<Predicate> lInitialState,
            Dictionary<string, CompoundFormula> dFormulas)
        {

            if (lLandmarkAchievers.Count == 0)
                return false;
            //looking for preconditions that are needed for all actions that achieve p
            HashSet<Predicate> lJointPreconditions = GetJointPreconditions(lLandmarkAchievers);
            bool bNewLandmarkFound = false;
            if (lJointPreconditions.Count > 0)
            {

                foreach (GroundedPredicate pPrecondition in lJointPreconditions)
                {
                    if (!lInitialState.Contains(pPrecondition))
                    {
                        string sPreconditionName = GetNameAndTag(pPrecondition);
                        if (!dFormulas.ContainsKey(sPreconditionName))
                            dFormulas[sPreconditionName] = new CompoundFormula("and");

                        dFormulas[sPreconditionName].AddOperand(pPrecondition);
                        bNewLandmarkFound = true;
                    }
                }

            }

            Dictionary<string, Dictionary<string, List<Predicate>>> dDisjunctions = GetDisjunctivePreconditions(lLandmarkAchievers, lInitialState);
            foreach (string sPredicateType in dDisjunctions.Keys)//go over the different pre types
            {
                Dictionary<string, List<Predicate>> dActionToPrecondition = dDisjunctions[sPredicateType];
                if (dActionToPrecondition.Count == lLandmarkAchievers.Count)//all achivers require a pre of this type
                {
                    if (!dFormulas.ContainsKey(sPredicateType))//allowing disjunctions only for predicate types where no joint preconditions exist
                    {
                        dFormulas[sPredicateType] = new CompoundFormula("or");
                        /*
                    else
                    {
                        CompoundFormula cfOr = new CompoundFormula("or");
                        cfOr.AddOperand(dFormulas[sPredicateType]);
                        dFormulas[sPredicateType] = cfOr;
                    }
                         * */
                        foreach (KeyValuePair<string, List<Predicate>> pair in dActionToPrecondition)
                        {
                            foreach (Predicate p in pair.Value)
                            {
                                if (!lInitialState.Contains(p))
                                {
                                    dFormulas[sPredicateType].AddOperand(p);
                                }
                            }
                        }
                    }
                }
            }



            return true;
        }

        private List<Formula> RegressLandmark(Formula fCurrentLandmark, Dictionary<Predicate, List<Action>> dLandmarkAchievers, HashSet<Predicate> lInitialState)
        {
            //when landmark is (or p1 p2), and p1 requires (or q1 q2) (or r1 r2) and p2 requires p3 and r3, then the result should be (or q1 q2 q3) (or r1 r2 r3)
            List<Formula> lFormulas = new List<Formula>();
            Dictionary<string, CompoundFormula> dAll = null;
            int cPredicatesToAchieve = 0;
            foreach (GroundedPredicate pLandmark in dLandmarkAchievers.Keys)
            {
                List<Action> lActions = dLandmarkAchievers[pLandmark];
                Dictionary<string, CompoundFormula> dRegressedFormulas = new Dictionary<string, CompoundFormula>();
                RegressLandmark(pLandmark, dLandmarkAchievers[pLandmark], lInitialState, dRegressedFormulas);
                string sLandmarkName = GetNameAndTag(pLandmark);
                if (dAll == null)
                    dAll = dRegressedFormulas;
                else
                {
                    Dictionary<string, CompoundFormula> dNew = new Dictionary<string, CompoundFormula>();
                    foreach (string sKey in dAll.Keys)
                    {
                        if (dRegressedFormulas.ContainsKey(sKey))
                        {
                            CompoundFormula cfOr = new CompoundFormula("or");
                            cfOr.AddOperand(dAll[sKey]);
                            cfOr.AddOperand(dRegressedFormulas[sKey]);
                            dNew[sKey] = cfOr;
                        }
                    }
                    dAll = dNew;
                }
            }
            foreach (string sPreType in dAll.Keys)
            {
                Formula fSimplified = dAll[sPreType].Simplify();
                //4 options here:
                //fSimplified is a single predicate
                //fSimplified is a simple disjunction
                //fSimplified is a simple conjunction
                //fSimplified is a disjunction of simple conjunctions
                if (fSimplified is PredicateFormula)
                    lFormulas.Add(fSimplified);
                else
                {
                    CompoundFormula cf = (CompoundFormula)fSimplified;
                    if (cf.Operator == "and")
                    {
                        foreach (PredicateFormula pf in cf.Operands)
                            lFormulas.Add(pf);
                    }
                    else
                        lFormulas.Add(RemoveConjunctions(cf));


                }

            }




            return lFormulas;
        }


        /*
         
        private bool RegressLandmark(Predicate pCurrentLandmark, List<Action> lLandmarkAchievers, HashSet<Predicate> lInitialState,
            Dictionary<string, List<Predicate>> dObligatory, Dictionary<string, List<Predicate>> dOptional)
        {

            if (lLandmarkAchievers.Count == 0)
                return false;
            //looking for preconditions that are needed for all actions that achieve p
            HashSet<Predicate> lJointPreconditions = GetJointPreconditions(lLandmarkAchievers);
            bool bNewLandmarkFound = false;
            if (lJointPreconditions.Count > 0)
            {
                foreach (GroundedPredicate pPrecondition in lJointPreconditions)
                {
                    if (!lInitialState.Contains(pPrecondition))
                    {
                        string sPreconditionName = GetNameAndTag(pPrecondition);
                        if (!dObligatory.ContainsKey(sPreconditionName))
                            dObligatory[sPreconditionName] = new List<Predicate>();

                        dObligatory[sPreconditionName].Add(pPrecondition);
                        bNewLandmarkFound = true;
                    }
                }

            }

            Dictionary<string, Dictionary<string, List<Predicate>>> dDisjunctions = GetDisjunctivePreconditions(lLandmarkAchievers, lInitialState);
            foreach (string sPredicateType in dDisjunctions.Keys)//go over the different pre types
            {
                Dictionary<string, List<Predicate>> dActionToPrecondition = dDisjunctions[sPredicateType];
                if (dActionToPrecondition.Count == lLandmarkAchievers.Count)//all achivers require a pre of this type
                {
                    if (!dOptional.ContainsKey(sPredicateType))
                        dOptional[sPredicateType] = new List<Predicate>();
                    foreach (KeyValuePair<string, List<Predicate>> pair in dActionToPrecondition)
                    {
                        foreach (Predicate p in pair.Value)
                        {
                            if (!lInitialState.Contains(p))
                            {
                                dOptional[sPredicateType].Add(p);
                            }
                        }
                    }
                }
            }



            return true;
        }

        private List<Formula> RegressLandmark(Formula fCurrentLandmark, Dictionary<Predicate, List<Action>> dLandmarkAchievers, HashSet<Predicate> lInitialState)
        {
            //when landmark is (or p1 p2), and p1 requires (or q1 q2) (or r1 r2) and p2 requires p3 and r3, then the result should be (or q1 q2 q3) (or r1 r2 r3)
            List<Formula> lFormulas = new List<Formula>();
            Dictionary<string, Dictionary<int, List<Predicate>>> dAllObligatory = new Dictionary<string, Dictionary<int, List<Predicate>>>();
            Dictionary<string, Dictionary<int, List<Predicate>>> dAllOptional = new Dictionary<string, Dictionary<int, List<Predicate>>>();
            int cPredicatesToAchieve = 0;
            foreach (GroundedPredicate pLandmark in dLandmarkAchievers.Keys)
            {
                List<Action> lActions = dLandmarkAchievers[pLandmark];
                Dictionary<string, List<Predicate>> dObligatory = new Dictionary<string, List<Predicate>>();
                Dictionary<string, List<Predicate>> dOptional = new Dictionary<string, List<Predicate>>();
                RegressLandmark(pLandmark, dLandmarkAchievers[pLandmark], lInitialState, dObligatory, dOptional);
                string sLandmarkName = GetNameAndTag(pLandmark);
                foreach (string sPreType in dObligatory.Keys)
                {
                    if (!dAllObligatory.ContainsKey(sPreType))
                        dAllObligatory[sPreType] = new Dictionary<int, List<Predicate>>();

                    dAllObligatory[sPreType][cPredicatesToAchieve] = new List<Predicate>();
                    dAllObligatory[sPreType][cPredicatesToAchieve].AddRange(dObligatory[sPreType]);
                }
                foreach (string sPreType in dOptional.Keys)
                {
                    if (!dAllOptional.ContainsKey(sPreType))
                        dAllOptional[sPreType] = new Dictionary<int, List<Predicate>>();

                    dAllOptional[sPreType][cPredicatesToAchieve] = new List<Predicate>();
                    dAllOptional[sPreType][cPredicatesToAchieve].AddRange(dOptional[sPreType]);
                }
                cPredicatesToAchieve++;
            }
            foreach (string sPreType in dAllObligatory.Keys)
            {
                if (dAllObligatory[sPreType].Count == cPredicatesToAchieve)
                {
                    CompoundFormula cfOr = new CompoundFormula("or");
                    foreach (List<Predicate> lPreconditions in dAllObligatory[sPreType].Values)
                    {
                        CompoundFormula cfAnd = new CompoundFormula("and");
                        foreach (Predicate p in lPreconditions)
                            cfAnd.AddOperand(p);
                        cfOr.AddOperand(cfAnd);
                    }
                    Formula fSimplified = cfOr.Simplify();
                    //4 options here:
                    //fSimplified is a single predicate
                    //fSimplified is a simple disjunction
                    //fSimplified is a simple conjunction
                    //fSimplified is a disjunction of simple conjunctions
                    if (fSimplified is PredicateFormula)
                        lFormulas.Add(fSimplified);
                    else
                    {
                        CompoundFormula cf = (CompoundFormula)fSimplified;
                        if (cf.Operator == "and")
                        {
                            foreach (PredicateFormula pf in cf.Operands)
                                lFormulas.Add(pf);
                        }
                        else
                            lFormulas.Add(RemoveConjunctions(cf));


                    }
                }
            }
            foreach (string sPreType in dAllOptional.Keys)
            {
                if (dAllOptional[sPreType].Count == cPredicatesToAchieve)
                {
                    CompoundFormula cfOr = new CompoundFormula("or");
                    foreach (List<Predicate> lPreconditions in dAllOptional[sPreType].Values)
                    {
                        CompoundFormula cfAnd = new CompoundFormula("or");
                        foreach (Predicate p in lPreconditions)
                            cfAnd.AddOperand(p);
                        cfOr.AddOperand(cfAnd);
                    }
                    Formula fSimplified = cfOr.Simplify();
                    //4 options here:
                    //fSimplified is a single predicate
                    //fSimplified is a simple disjunction
                    //fSimplified is a simple conjunction
                    //fSimplified is a disjunction of simple conjunctions
                    if (fSimplified is PredicateFormula)
                        lFormulas.Add(fSimplified);
                    else
                    {
                        CompoundFormula cf = (CompoundFormula)fSimplified;
                        if (cf.Operator == "and")
                        {
                            foreach (PredicateFormula pf in cf.Operands)
                                lFormulas.Add(pf);
                        }
                        else
                            lFormulas.Add(RemoveConjunctions(cf));


                    }
                }
            }


            return lFormulas;
        }


         */

        private CompoundFormula RemoveConjunctions(CompoundFormula cf)
        {
            CompoundFormula cfNew = new CompoundFormula("or");
            if (cf.Operator == "and")
            {
                foreach (PredicateFormula pf in cf.Operands)
                    cfNew.AddOperand(pf);
            }
            else
            {
                foreach (Formula fSub in cf.Operands)
                {
                    if (fSub is PredicateFormula)
                        cfNew.AddOperand(fSub);
                    else
                        cfNew.AddOperand(RemoveConjunctions((CompoundFormula)fSub));
                }
            }
            return cfNew;
        }

        private string GetNameAndTag(GroundedPredicate p)
        {
            string sName = p.Name;
            if (sName.StartsWith("Given"))
                sName = sName + "." + p.Constants.Last().Name;
            return sName;

        }

        private Dictionary<Predicate, List<Action>> GetLandmarkAchievers(Formula fLandmark, HashSet<Predicate> lAllReachable, List<Action> lPotentialLandmarkAchievers)
        {
            Dictionary<Predicate, List<Action>> dActions = new Dictionary<Predicate, List<Action>>();
            HashSet<Predicate> lLandmark = fLandmark.GetAllPredicates();
            foreach (Predicate p in lLandmark)
            {
                dActions[p] = new List<Action>();
                foreach (Action a in lPotentialLandmarkAchievers)
                {
                    if (a.Preconditions.IsTrue(lAllReachable))
                    {
                        Formula fEffects = a.GetApplicableEffects(lAllReachable, false);
                        HashSet<Predicate> lEffects = fEffects.GetAllPredicates();
                        if (lEffects.Contains(p))
                        {
                            dActions[p].Add(a);
                        }
                    }
                }

            }
            return dActions;
        }

        private HashSet<Predicate> ReachablePredicates(HashSet<Predicate> lInitial, List<Action> lFiltered)
        {
            HashSet<Predicate> lReachable = new HashSet<Predicate>(lInitial);
            List<Action> lUnapplied = new List<Action>(lFiltered);
            bool bChanged = true;
            while (bChanged)
            {
                bChanged = false;
                List<Action> lNewUnapplied = new List<Action>();
                foreach (Action a in lUnapplied)
                {
                    //if (a.Name.Contains("p3-1") && a.Name.Contains("smell"))
                    //    Debug.WriteLine("*");
                    if (a.Preconditions.IsTrue(lReachable, true))
                    {
                        Formula f = a.GetApplicableEffects(lReachable, true);
                        HashSet<Predicate> lEffects = f.GetAllPredicates();
                        foreach (Predicate p in lEffects)
                        {
                            if (lReachable.Add(p))
                                bChanged = true;
                        }
                    }
                    else
                        lNewUnapplied.Add(a);
                }
                lUnapplied = lNewUnapplied;
            }
            return lReachable;
        }

        private void FilterActions(List<Action> lGrounded, Formula fCurrent, List<Action> lFiltered, List<Action> lLandmarkAchievers)
        {
            HashSet<Predicate> lLandmark = fCurrent.GetAllPredicates();
            foreach (Action a in lGrounded)
            {
                HashSet<Predicate> lConditionalEffects = new HashSet<Predicate>(), lNonConditionalEffects = new HashSet<Predicate>();
                a.Effects.GetAllEffectPredicates(lConditionalEffects, lNonConditionalEffects);
                bool bAchieveLandmark = false;
                foreach (Predicate p in lLandmark)
                {
                    if (lConditionalEffects.Contains(p) || lNonConditionalEffects.Contains(p))
                    {
                        bAchieveLandmark = true;
                        break;
                    }
                }
                if (bAchieveLandmark)
                    lLandmarkAchievers.Add(a);
                else
                    lFiltered.Add(a);
            }
        }


        private void FilterActions(List<Action> lGrounded, Formula fCurrent, List<Action> lFiltered, List<Action> lLandmarkAchievers,
            Dictionary<Predicate, List<Action>> dPreconditionToAction, Dictionary<Predicate, List<Action>> dEffectToAction,
            HashSet<Predicate> lInitialState)
        {
            HashSet<Predicate> lLandmark = fCurrent.GetAllPredicates();
            HashSet<string> hsPreNames = new HashSet<string>();
            HashSet<string> hsEffectNames = new HashSet<string>();
            foreach (Predicate p in lLandmark)
            {
                if (!lInitialState.Contains(p))
                {
                    if (dPreconditionToAction.ContainsKey(p))
                    {
                        foreach (Action a in dPreconditionToAction[p])
                            hsPreNames.Add(a.Name);
                    }
                }
                if (dEffectToAction.ContainsKey(p))
                {
                    foreach (Action a in dEffectToAction[p])
                        hsEffectNames.Add(a.Name);
                }
            }

            foreach (Action a in lGrounded)
            {
                //if (a.Name.Contains("p3-1") && a.Name.Contains("smell"))
                //   Debug.WriteLine("*");

                if (hsEffectNames.Contains(a.Name))
                    lLandmarkAchievers.Add(a);
                else if (!hsPreNames.Contains(a.Name))
                    lFiltered.Add(a);
            }
        }

        public List<Action> SolveII(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            List<State> lOpenList = new List<State>();
            lOpenList.Add(sStart);
            State sCurrent = null, sNext = null;
            Dictionary<State, Action> dMapStateToGeneratingAction = new Dictionary<State, Action>();
            dMapStateToGeneratingAction[sStart] = null;
            Dictionary<State, State> dParents = new Dictionary<State, State>();
            Dictionary<State, int> dDepth = new Dictionary<State, int>();
            dDepth[sStart] = 0;
            dParents[sStart] = null;
            int cProcessed = 0;
            List<string> lActionNames = new List<string>();
            while (lOpenList.Count > 0)
            {
                sCurrent = lOpenList[0];
                lOpenList.RemoveAt(0);
                List<Action> lActions = d.GroundAllActions(sCurrent.Predicates, false);
                foreach (Action a in lActions)
                {
                    sNext = sCurrent.Apply(a);
                    bool bGiven = false;
                    foreach (Predicate pGiven in sNext.Predicates)
                    {
                        if (pGiven.Name.ToLower().Contains("given"))
                            bGiven = true;
                    }
                    if (!lActionNames.Contains(a.Name))
                        lActionNames.Add(a.Name);
                    if (sNext != null && p.IsGoalState(sNext))
                        return GeneratePlan(sCurrent, a, dParents, dMapStateToGeneratingAction);
                    if (!dParents.Keys.Contains(sNext))
                    {
                        dDepth[sNext] = dDepth[sCurrent] + 1;
                        dParents[sNext] = sCurrent;
                        dMapStateToGeneratingAction[sNext] = a;
                        lOpenList.Add(sNext);
                    }
                }
                cProcessed++;
                if (cProcessed % 10 == 0)
                    Debug.WriteLine(cProcessed + ") " + dDepth[sCurrent] + "," + lOpenList.Count);
            }
            return null;
        }

        public List<Action> ManualSolve(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            State sCurrent = null, sNext = null;
            Dictionary<State, Action> dMapStateToGeneratingAction = new Dictionary<State, Action>();
            dMapStateToGeneratingAction[sStart] = null;
            Dictionary<State, State> dParents = new Dictionary<State, State>();
            dParents[sStart] = null;
            int cProcessed = 0;
            List<string> lActionNames = new List<string>();

            sCurrent = sStart;
            while (!p.IsGoalState(sCurrent))
            {
                List<Action> lActions = d.GroundAllActions(sCurrent.Predicates, false);
                Debug.WriteLine("Available actions:");
                for (int i = 0; i < lActions.Count; i++)
                {
                    Debug.WriteLine(i + ") " + lActions[i].Name);
                }
                Debug.Write("Choose action number: ");
                int iAction = int.Parse(Console.ReadLine());
                Action a = lActions[iAction];
                sNext = sCurrent.Apply(a);

                foreach (Predicate pNew in sNext.Predicates)
                    if (!sCurrent.Predicates.Contains(pNew))
                        Debug.WriteLine(pNew);

                if (!dParents.Keys.Contains(sNext))
                {
                    dParents[sNext] = sCurrent;
                    dMapStateToGeneratingAction[sNext] = a;
                }

                sCurrent = sNext;

                cProcessed++;
            }
            return GeneratePlan(sCurrent, null, dParents, dMapStateToGeneratingAction);
        }


        public List<Action> RadnomSolve(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            List<Action> lActions = d.GroundAllActions(sStart.Predicates, false);
            int iRnd = RandomGenerator.Next(lActions.Count);
            List<Action> lPlan = new List<Action>();
            lPlan.Add(lActions[iRnd]);
            return lPlan;
        }

        public List<Action> Solve(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            List<Action> lActions = new List<Action>();
            Action aClear = d.GroundActionByName(new string[] { "clear-all", "" }, sStart.Predicates, false);
            sStart = sStart.Apply(aClear);
            lActions.Add(aClear);
            State sComputeUpstream = ApplyCompute(sStart, "upstream", lActions, d);
            State sComputeAffected = ApplyCompute(sComputeUpstream, "affected", lActions, d);
            State sComputePath = ApplyCompute(sComputeAffected, "path", lActions, d);
            State sComputeLine = ApplyCompute(sComputePath, "line", lActions, d);
            //State sObserveAll = ObserveAll(sComputeLine, lActions, d);
            return lActions;
        }

        public List<Action> SolveOld(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            List<Action> lActions = new List<Action>();
            State sObserved = ObserveAll(sStart, lActions, d);
            State sFixed = ApplyAxiom(sObserved, lActions, d);
            //State sClosed = CloseAll(sFixed, lActions, d);
            //State sFixed2 = ApplyAxiom(sClosed, lActions, d);
            State sObserved2 = ObserveAll(sFixed, lActions, d);
            return lActions;
        }

        private State CloseAll(State s, List<Action> lActions, Domain d)
        {
            State sCurrent = s;
            List<Action> l = d.GroundAllActions(s.Predicates, false);
            foreach (Action a in l)
            {
                if (a.Name.Contains("close"))
                {
                    sCurrent = sCurrent.Apply(a);
                    lActions.Add(a);
                }
            }
            return sCurrent;
        }

        private State ApplyCompute(State s, string sName, List<Action> lActions, Domain d)
        {
            State sCurrent = s;
            Predicate pNew = new GroundedPredicate("new-" + sName);
            Predicate pDone = new GroundedPredicate("done-" + sName);
            int i = 0;
            while (!sCurrent.Contains(pNew.Negate()) || !sCurrent.Contains(pDone) || i < 10)
            {
                Action a1 = d.GroundActionByName(new string[] { "pre-" + sName, "" }, sCurrent.Predicates, false);
                Action a2 = d.GroundActionByName(new string[] { "compute-" + sName, "" }, sCurrent.Predicates, false);
                if (a1 != null && a2 != null)
                {
                    sCurrent = sCurrent.Apply(a1);
                    sCurrent = sCurrent.Apply(a2);
                    lActions.Add(a1);
                    lActions.Add(a2);
                }
                i++;
            }

            Action a = d.GroundActionByName(new string[] { "observe-new-" + sName + "-F", "" }, sCurrent.Predicates, false);
            sCurrent = sCurrent.Apply(a);
            lActions.Add(a);

            a = d.GroundActionByName(new string[] { "post-" + sName, "" }, sCurrent.Predicates, false);
            sCurrent = sCurrent.Apply(a);
            lActions.Add(a);

            return sCurrent;
        }

        private State ApplyAxiom(State s, List<Action> lActions, Domain d)
        {
            State sCurrent = s;
            Predicate pNew = new GroundedPredicate("new");
            Predicate pDone = new GroundedPredicate("done");
            while (!sCurrent.Contains(pNew.Negate()) || !sCurrent.Contains(pDone))
            {
                Action a1 = d.GroundActionByName(new string[] { "pre-axiom", "" }, sCurrent.Predicates, false);
                Action a2 = d.GroundActionByName(new string[] { "axiom", "" }, sCurrent.Predicates, false);
                if (a1 != null && a2 != null)
                {
                    sCurrent = sCurrent.Apply(a1);
                    sCurrent = sCurrent.Apply(a2);
                    lActions.Add(a1);
                    lActions.Add(a2);
                }
            }

            Action a = d.GroundActionByName(new string[] { "observe-new-F", "" }, sCurrent.Predicates, false);
            sCurrent = sCurrent.Apply(a);
            lActions.Add(a);

            a = d.GroundActionByName(new string[] { "fixpoint", "" }, sCurrent.Predicates, false);
            sCurrent = sCurrent.Apply(a);
            lActions.Add(a);

            return sCurrent;
        }

        private State ObserveAll(State s, List<Action> lActions, Domain d)
        {
            State sCurrent = s;
            List<Action> l = d.GroundAllActions(s.Predicates, false);
            foreach (Action a in l)
            {
                if (a.Name.Contains("observe"))
                {
                    sCurrent = sCurrent.Apply(a);
                    lActions.Add(a);
                }
            }
            return sCurrent;
        }

        private List<Action> GeneratePlan(State sBeforeLast, Action aLast, Dictionary<State, State> dParents, Dictionary<State, Action> dMapStateToGeneratingAction)
        {
            List<Action> lPlan = new List<Action>();
            State sCurrent = sBeforeLast;
            lPlan.Add(aLast);
            while (dParents[sCurrent] != null)
            {
                Action a = dMapStateToGeneratingAction[sCurrent];
                lPlan.Add(a);
                sCurrent = dParents[sCurrent];
            }
            lPlan.Reverse();
            return lPlan;
        }
    }
}
