# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| AdjacencyPermanentMatchingCount | lemma | proof | closed | - | - | PerfectMatching |
| AuxiliarySpreadExecution | lemma | proof | closed | - | - | EqualSizeParameterTable, EqualSizeTerminalConversion, SuperRegularErrorMonotone, VariableSizeInductionIteration |
| BalancedDegreeVarianceBound | lemma | proof | closed | - | Balanced restricted-degree variance | Preamble |
| BennettEntropyLowerBound | helper | proof | closed | - | Bennett entropy lower bound | Preamble |
| BijectionCompletionCount | helper | proof | closed | - | Counting completions of prescribed images | Preamble |
| BipartiteFactorCutCapacity | lemma | proof | closed | - | All cuts of the factor network | BipartiteFactorNetwork |
| BipartiteFactorNetwork | definition | definition | closed | - | Network for a bipartite regular factor | FiniteCapacityNetwork |
| BipartiteFlowSaturation | lemma | proof | closed | - | Saturation and selected middle edges | BipartiteFactorNetwork, FiniteIntegralFlow |
| BipartiteRectangleDegreeBound | lemma | proof | closed | - | Degree counting inside a rectangle | FilteredProductRowCount |
| BipartiteRegularFactorCriterion | lemma | proof | closed | - | Bipartite regular-factor cut criterion | BipartiteFactorCutCapacity, BipartiteFlowSaturation, BipartiteRectangleDegreeBound, BipartiteSelectedEdgeGraph, IntegralFlowTerminalCut, Preamble, RectangleFactorCutLowerBound |
| BipartiteSelectedEdgeGraph | lemma | proof | closed | - | Transporting distinct selected pairs to a simple graph | Preamble |
| BlowUpInstance | definition | definition | closed | - | - | Preamble |
| BlowUpReductionToAuxiliary | lemma | proof | closed | - | Reduction to the auxiliary blow-up lemma | EquitableSquareColoring, MatchingCompletionExtension, RegularSubgraph, SimultaneousHostCandidacyRefinement, SuperRegularSubgraph |
| BlowupOrderMargins | lemma | proof | closed | - | - | Preamble |
| BregmanMatchingDegreeProduct | lemma | proof | closed | - | Matching row-degree product | AdjacencyPermanentMatchingCount |
| CandidacyLowerSuperRegular | definition | definition | closed | - | - | CandidacySystem, LowerSuperRegularPair |
| CandidacySuperRegular | definition | definition | closed | - | - | CandidacySystem, SuperRegularPair |
| CandidacySystem | definition | definition | closed | - | - | BlowUpInstance |
| CapacityPreservingReassignment | lemma | proof | closed | - | Capacity-preserving reassignment of exceptions | Preamble |
| ClusterRebalancing | lemma | proof | closed | - | Cluster rebalancing | CandidacyLowerSuperRegular, ClusterwiseDeletionBuffer, ExceptionalLeftLowerSuperRegular, InstanceLowerSuperRegular, LowerSuperRegularDeletionSlicing, RebalancingLossMargins, RebalancingResidualCandidacy, RebalancingResidualGeometry, RebalancingResidualHost, RebalancingRestrictionEstimates, RestrictedPartialEmbeddingTransport, RestrictedSmallBlowUpInterface |
| ClusterwiseDeletionBuffer | lemma | proof | closed | - | Clusterwise deletion and its external buffer | BlowUpInstance |
| CodegreeWindowTransfer | lemma | proof | closed | - | Transfer of neighborhood bounds to a codegree window | Preamble |
| ColourClassSequentialCompletion | lemma | proof | closed | - | Sequential completion of a colour class | ColourRoundInvariant |
| ColourRoundInvariant | definition | definition | closed | - | Colour-round induction invariant | PartialCompatibleEmbedding, SuperRegularPair, UpdatedCandidacyCluster, VertexSpreadOn |
| ColourRoundKernelAssembly | lemma | proof | closed | - | Assembly of locally certified extension laws | ColourRoundInvariant, ColourRoundUntouchedGeometry, ExtendUpdatedPartialEmbedding, UpdatedCandidacyNonneighborExtension, VertexSpreadRestriction |
| ColourRoundMatchingPreparation | lemma | proof | closed | - | Retained triplets and local success law | ColourRoundInvariant, ColourRoundMatchingRecords, ColourRoundRetainedTriplets, ColourRoundStepParameters, ColourRoundUntouchedGeometry, CurrentExtraSourceWitnessTransport, EqualSizeSourceWitnessTransport, FiniteTripletRelabelling, FutureExtraSourceWitnessTransport, InstanceSuperRegular, NearEqualVaryingGoodEdgeSuperRegularity, OneClusterExtension, SaturatingSourcePair, VertexSpreadMonotone |
| ColourRoundMatchingRecords | lemma | proof | closed | - | Matching records and true updated containment | ColourRoundInvariant, PerfectMatching |
| ColourRoundReset | lemma | proof | closed | - | Reset between consecutive colour rounds | ColourRoundInvariant |
| ColourRoundRetainedTriplets | lemma | proof | closed | - | Deterministic retained triplet family | ColourRoundInvariant, ColourRoundSourceWitnessAssembly, ColourRoundStepParameters, ColourRoundUntouchedGeometry, ColourRoundWitnessThinnings, CurrentExtraSourceWitnessTransport, EqualSizeSourceWitnessTransport, FiniteTripletRelabelling, FutureExtraSourceWitnessTransport, InstanceSuperRegular, NearEqualVaryingGoodEdgeSuperRegularity, SaturatingSourcePair |
| ColourRoundSourceWitnessAssembly | lemma | proof | closed | - | Source-matching assembly of a future test | ColourRoundStepParameters, CurrentExtraSourceWitnessTransport, EqualSizeSourceWitnessTransport, FutureExtraSourceWitnessTransport, SaturatingSourcePair |
| ColourRoundStepParameters | definition | definition | closed | - | Numerical data for one colour round | InductionApplicationCertificate |
| ColourRoundUntouchedGeometry | lemma | proof | closed | - | Untouched witnesses and independent exposure counts | ReducedSquareColoring |
| ColourRoundWitnessThinnings | lemma | proof | closed | - | Contained thinnings of the full untouched witnesses | ColourRoundInvariant, ColourRoundStepParameters, ColourRoundUntouchedGeometry, FiniteSuperRegularThinning, InstanceSuperRegular, SuperRegularPairEmbedding |
| CompatibleEmbedding | definition | definition | closed | - | - | CandidacySystem |
| CompleteRowPadding | lemma | proof | closed | - | Lower super-regularity under complete-row padding | LowerSuperRegularPair |
| CrossEdgeRetention | definition | definition | closed | - | Spanning cross-edge retention | Preamble |
| CrossEdgeRetentionCounts | lemma | proof | closed | - | Exact counts on the common retention sample | CrossEdgeRetention, IndependentRetentionCount |
| CrossPairSubgraphAssembly | lemma | proof | closed | - | Assembly of contained crossing subgraphs | SuperRegularPair, SuperRegularPairEmbedding |
| CurrentExtraSourceWitnessTransport | lemma | proof | closed | - | Artificial current row, deletion, and contained transport | FutureExtraVertexStability, MatchingInducedLeftRowDeletion, MatchingInducedUpdatedCandidacyTransport |
| CylinderEvent | definition | definition | closed | - | - | Preamble |
| DegreeCodegreeRegularityCriterion | lemma | proof | closed | - | Degree--codegree criterion | BalancedDegreeVarianceBound, FilteredProductRowCount, OrderedTwoPathCount, RegularPair |
| DirectedReachabilitySimplePath | lemma | proof | closed | - | Removing repetitions from a directed residual walk | Preamble |
| ElementarySymmetricExtremaStep | lemma | proof | closed | - | Extrema averaging contracts variance | ElementarySymmetricPairAveraging |
| ElementarySymmetricMean | lemma | proof | closed | - | Elementary-symmetric mean inequality | ElementarySymmetricExtremaStep, Preamble |
| ElementarySymmetricPairAveraging | lemma | proof | closed | - | One pair-averaging step | Preamble |
| EqualSizeBackwardCertificates | lemma | proof | closed | - | Backward colour-round certificates | EqualSizeOneRoundChoices, SuperRegularErrorMonotone |
| EqualSizeCommonOrderBounds | lemma | proof | closed | - | Common constants and uniform order bounds | InductionApplicationCertificate |
| EqualSizeOneRoundChoices | lemma | proof | closed | - | Simultaneous choices for one colour round | InductionApplicationCertificate, MatchingEnumeration, NearEqualFourGraphs, QuantitativeSuperRegularThinning, UniformPerfectMatchingSpread |
| EqualSizeParameterTable | lemma | proof | closed | - | Finite colour-round parameter construction | EqualSizeBackwardCertificates, EqualSizeCommonOrderBounds, ExposureDensityRecursion |
| EqualSizeSourceWitnessTransport | lemma | proof | closed | - | Equal-size pullback and contained transport | MatchingInducedUpdatedCandidacyTransport |
| EqualSizeTerminalConversion | lemma | proof | closed | - | Full-domain terminal conversion | PartialCompatibleEmbedding, VertexSpreadOn, VertexSpreadRestriction |
| EquitableSquareColoring | lemma | proof | closed | - | Equitable square coloring | BlowUpInstance |
| ExceptionalCoreEdgeExtension | lemma | proof | closed | - | Extending a core by exceptional rows | Preamble |
| ExceptionalLeftLowerSuperRegular | lemma | proof | closed | - | Exceptional-row slicing for a candidacy pair | LowerSuperRegularPair, PairDensity |
| ExceptionalRectangleDensity | lemma | proof | closed | - | Density after exceptional-position changes | PairDensityReal |
| ExposureDensityRecursion | lemma | proof | closed | - | Exposure densities and their positive gaps | Preamble |
| ExtendUpdatedPartialEmbedding | lemma | proof | closed | - | Extension by an updated partial embedding | UpdatedCandidacy |
| ExtractionTailCutoffs | lemma | proof | closed | - | Uniform extraction tail cutoffs | Preamble |
| FactorialRootExceptionalProduct | lemma | proof | closed | - | Factorial-root product with exceptional rows | FactorialRootMonotone, LogFactorialBounds, Preamble |
| FactorialRootMonotone | lemma | proof | closed | - | Monotonicity of positive factorial roots | Preamble |
| FiberwiseCapacityRefinement | lemma | proof | closed | - | Refining finite capacities by colors | Preamble |
| FilteredProductRowCount | lemma | proof | closed | - | Counting a relation by rows | Preamble |
| FiniteCapacityNetwork | definition | definition | closed | - | Finite integer-capacity network | Preamble |
| FiniteGreedySpreadLaw | lemma | proof | closed | - | Finite greedy law with random total-map completion | VertexSpreadRestriction, VertexSpreadSequential |
| FiniteIndependentSubgaussianTail | lemma | proof | closed | - | Finite independent subgaussian tail | Preamble |
| FiniteIntegralFlow | definition | definition | closed | - | Feasible integral net flow | FiniteCapacityNetwork |
| FinitePartialMatchingCompletion | lemma | proof | closed | - | Completion of a finite partial matching | Preamble |
| FiniteSuperRegularThinning | lemma | proof | closed | - | Universe-independent finite thinning | FiniteTripletRelabelling |
| FiniteTripletRelabelling | lemma | proof | closed | - | Relabelling triplets and their matching intersections | MatchingInducedGraph, NearEqualRegularTriplet, PerfectMatching, SuperRegularPairEmbedding |
| FourGraphsPolynomialLossAbsorption | lemma | proof | closed | - | Absorbing the Four Graphs polynomial loss | Preamble |
| FourRectangleFactorialCancellation | lemma | proof | closed | - | Four-rectangle factorial cancellation | Preamble |
| FourRectangleMatchingFiberBound | lemma | proof | closed | - | Counting four-rectangle matching fibers | FourRectangleMatchingPartition, MatchingPartitionRestrictionCount, PerfectMatching |
| FourRectangleMatchingPartition | lemma | proof | closed | - | The canonical four-rectangle partition | Preamble |
| FourRectangleSmallOrderProduct | lemma | proof | closed | - | Loss from small matching rectangles | Preamble |
| FutureExtraSourceWitnessTransport | lemma | proof | closed | - | Residual future transport and genuine row restoration | FutureExtraVertexStability, MatchingInducedLeftRowDeletion, MatchingInducedUpdatedCandidacyTransport |
| FutureExtraVertexStability | lemma | proof | closed | - | Adjoining one exceptional row to a near-equal super-regular pair | SuperRegularPair |
| GreedyPartialEmbedding | definition | definition | closed | - | Greedy partial-embedding state | PartialCompatibleEmbedding, RawCandidates |
| GreedyPartialEmbeddingReserve | lemma | proof | closed | - | Clusterwise reserve of a greedy state | GreedyPartialEmbedding, UpdatedCandidacy |
| GreedyPartialEmbeddingStep | lemma | proof | closed | - | One-vertex greedy extension | GreedyPartialEmbedding, InstanceLowerRegular, LowerRegularBadRows |
| HostExceptionalCorrection | lemma | proof | closed | - | Suitable-bin correction of exceptional host vertices | BlowUpInstance, CandidacyLowerSuperRegular, CandidacySystem, CapacityPreservingReassignment, FilteredProductRowCount |
| HostRefinementParameters | lemma | proof | closed | - | Parameters for host refinement | Preamble |
| HypergeometricExponentialMoment | lemma | proof | closed | - | Centered hypergeometric exponential moment | ElementarySymmetricMean, HypergeometricMass, WeightedSubsetIntersectionSum |
| HypergeometricMass | definition | definition | closed | - | Hypergeometric masses | Preamble |
| HypergeometricTwoTail | lemma | proof | closed | - | Two hypergeometric tails | BennettEntropyLowerBound, HypergeometricExponentialMoment, NegativeExponentialQuadraticBound |
| IndependentEdgeSample | definition | definition | closed | - | Common independent retention sample | Preamble |
| IndependentRetentionConcentration | lemma | proof | closed | - | Two-sided concentration for one retention test | IndependentEdgeSample, IndependentRetentionCount, IndependentUnequalEdgeSampleLaw |
| IndependentRetentionCount | definition | definition | closed | - | Retained coordinate count | Preamble |
| IndependentUnequalEdgeSampleLaw | lemma | proof | closed | - | Independent unequal Bernoulli law | Preamble |
| InductionApplicationCertificate | definition | definition | closed | - | - | MatchingEnumeration, NearEqualFourGraphs, QuantitativeSuperRegularThinning, UniformPerfectMatchingSpread |
| InstanceLowerRegular | definition | definition | closed | - | - | BlowUpInstance, LowerRegularPair |
| InstanceLowerSuperRegular | definition | definition | closed | - | - | BlowUpInstance, LowerSuperRegularPair |
| InstanceSuperRegular | definition | definition | closed | - | - | BlowUpInstance, SuperRegularPair |
| IntegralFlowAugmentation | lemma | proof | closed | - | Integral augmentation along a simple residual path | SimpleResidualPath |
| IntegralFlowCutIdentity | lemma | proof | closed | - | Net flow across a cut | FiniteIntegralFlow |
| IntegralFlowTerminalCut | lemma | proof | closed | - | Termination and a tight residual cut | DirectedReachabilitySimplePath, IntegralFlowAugmentation, IntegralFlowCutIdentity |
| LogFactorialBounds | lemma | proof | closed | - | Elementary logarithmic factorial bounds | Preamble |
| LowerRegularBadRows | lemma | proof | closed | - | Bad rows of a lower-regular pair | FilteredProductRowCount, LowerRegularPair |
| LowerRegularPair | definition | definition | closed | - | - | PairDensity |
| LowerRegularRestriction | lemma | proof | closed | - | Threshold transfer to restricted parts | LowerRegularPair |
| LowerSuperRegularDeletionSlicing | lemma | proof | closed | - | Lower-super-regular slicing after deletion | LowerSuperRegularPair |
| LowerSuperRegularPair | definition | definition | closed | - | - | LowerRegularPair |
| LowerSuperRegularPairEmbedding | lemma | proof | closed | - | Transport of a lower super-regular pair | LowerSuperRegularPair |
| MatchingCompletionExtension | lemma | proof | closed | - | Simultaneous matching completion | BlowUpInstance, FiberwiseCapacityRefinement, FinitePartialMatchingCompletion, SaturatingSourcePair |
| MatchingConcentrationCorrection | definition | definition | closed | - | Logarithmic matching-count correction | Preamble |
| MatchingConcentrationCorrectionAbsorption | lemma | proof | closed | - | Correction limit and exponential absorption | MatchingConcentrationCorrection |
| MatchingEnumeration | lemma | proof | closed | - | Perfect-matching enumeration | PerfectMatching, RegularBipartiteMatchingCount, SuperRegularPair, SuperRegularSpanningFactor |
| MatchingInducedCodegreeConcentration | lemma | proof | closed | - | Simultaneous good-pair codegrees from set-image concentration | MatchingInducedGraphIdentities, PerfectMatching |
| MatchingInducedDegreeConcentration | lemma | proof | closed | - | Simultaneous right degrees from set-image concentration | MatchingInducedGraphIdentities, PerfectMatching, SuperRegularPair |
| MatchingInducedGraph | definition | definition | closed | - | - | PerfectMatching |
| MatchingInducedGraphIdentities | lemma | proof | closed | - | Copied matching-induced degree and codegree identities | MatchingInducedGraph |
| MatchingInducedLeftRowDeletion | lemma | proof | closed | - | Deleting one row from a near-equal super-regular pair | SuperRegularPair |
| MatchingInducedSuperRegularCertificate | lemma | proof | closed | - | A deterministic certificate for the matching-induced graph | MatchingInducedGraphIdentities, NearEqualDegreeCodegreeRegularityCriterion, NearEqualRegularTriplet |
| MatchingInducedUpdatedCandidacyTransport | lemma | proof | closed | - | Transport of the matching-induced candidacy graph | MatchingInducedGraph, PerfectMatching, SuperRegularPair, UpdatedCandidacyCluster |
| MatchingManyEdges | lemma | proof | closed | - | Many prescribed matching edges | BijectionCompletionCount, CylinderEvent, MatchingEnumeration, UniformPerfectMatching |
| MatchingPartitionRestrictionCount | lemma | proof | closed | - | Counting by four matching restrictions | PerfectMatching |
| MatchingSwitchCandidateCount | lemma | proof | closed | - | Outgoing switching candidates | PerfectMatching, SuperRegularPair |
| MatchingSwitching | lemma | proof | closed | - | Conditional switching estimate | CylinderEvent, MatchingSwitchCandidateCount, MatchingThreeEdgeSwitchIncoming, MatchingThreeEdgeSwitchInjective, MatchingThreeEdgeSwitchValid, SuperRegularPair, UniformPerfectMatching |
| MatchingThreeEdgeSwitch | definition | definition | closed | - | Three-edge switching map | Preamble |
| MatchingThreeEdgeSwitchIncoming | lemma | proof | closed | - | Incoming reconstruction from the third matching edge | MatchingThreeEdgeSwitchProperties |
| MatchingThreeEdgeSwitchInjective | lemma | proof | closed | - | Outgoing switches have distinct resulting matchings | MatchingThreeEdgeSwitchProperties |
| MatchingThreeEdgeSwitchProperties | lemma | proof | closed | - | Values and bijectivity of a three-edge switch | MatchingThreeEdgeSwitch |
| MatchingThreeEdgeSwitchValid | lemma | proof | closed | - | A valid three-edge switching preserves prescribed entries | MatchingThreeEdgeSwitchProperties, PerfectMatching |
| NearEqualDegreeCodegreeRegularityCriterion | lemma | proof | closed | - | Near-equal degree--codegree criterion | FilteredProductRowCount, OrderedTwoPathCount, RegularPair, RestrictedDegreeVarianceBound |
| NearEqualFourGraphs | lemma | proof | closed | - | Near-equal Four Graphs lemma | FourGraphsPolynomialLossAbsorption, MatchingEnumeration, MatchingInducedCodegreeConcentration, MatchingInducedDegreeConcentration, MatchingInducedGraph, MatchingInducedSuperRegularCertificate, NearEqualDegreeCodegreeRegularityCriterion, NearEqualFourGraphsParameters, NearEqualRegularPairGoodCodegrees, NearEqualRegularTriplet, SuperRegularPair, UniformMatchingSetImageConcentration, UniformPerfectMatching |
| NearEqualFourGraphsParameters | lemma | proof | closed | - | Four Graphs parameter windows | Preamble |
| NearEqualRegularPairGoodCodegrees | lemma | proof | closed | - | Good codegrees in a near-equal regular pair | SuperRegularCodegreeExceptionalBound |
| NearEqualRegularTriplet | definition | definition | closed | - | - | SuperRegularPair |
| NearEqualRetentionThreshold | lemma | proof | closed | - | Uniform numerical threshold for near-equal retention tests | Preamble |
| NearEqualSuperRegularExtraction | lemma | proof | closed | - | Contained extraction on equal or consecutive parts | CompleteRowPadding, LowerSuperRegularPairEmbedding, SuperRegularPairEmbedding, SuperRegularPairOneVertexDeletion, SuperRegularSubgraph |
| NearEqualVaryingGoodEdgeSuperRegularity | lemma | proof | closed | - | Near-equal varying-error simultaneous good-edge retention | CodegreeWindowTransfer, OneIndexBadPairCounting, RegularPairLowerTail, RegularPairUpperTail, RegularityAfterDensityLoss, SimultaneousGoodEdgeGraph, SmallNeighborhoodCodegreeWindow, SuperRegularPair |
| NegativeExponentialQuadraticBound | helper | proof | closed | - | Quadratic bound for a negative exponential parameter | Preamble |
| OneClusterExtension | lemma | proof | closed | - | One-cluster extension | NearEqualFourGraphs, NearEqualRegularTriplet, UniformPerfectMatchingSpread, VertexSpreadConditioning |
| OneIndexBadPairCounting | lemma | proof | closed | - | One-index near-equal bad-pair counting | CodegreeWindowTransfer, RegularPairLowerTail, RegularPairUpperTail, SmallNeighborhoodCodegreeWindow, SuperRegularPair |
| OrderedTwoPathCount | lemma | proof | closed | - | Counting ordered two-edge paths | Preamble |
| PaddedSource | definition | definition | closed | - | - | BlowUpInstance |
| PairDensity | definition | definition | closed | - | - | Preamble |
| PairDensityReal | lemma | proof | closed | - | Real density adapter | PairDensity |
| PartialCompatibleEmbedding | definition | definition | closed | - | - | CompatibleEmbedding |
| PartialEmbedding | lemma | proof | closed | - | Partial embedding lemma | FiniteGreedySpreadLaw, GreedyPartialEmbeddingReserve, GreedyPartialEmbeddingStep, InstanceLowerRegular, PartialEmbeddingParameters, UpdatedCandidacyCluster, UpdatedCandidacyCongruence, VertexSpreadSequential |
| PartialEmbeddingParameters | lemma | proof | closed | - | Parameters for the partial-embedding construction | Preamble |
| PerfectMatching | definition | definition | closed | - | - | Preamble |
| PerfectMatchingBijectionBound | lemma | proof | closed | - | The elementary matching upper bound | PerfectMatching |
| Preamble | preamble | preamble | closed | - | - | - |
| PrescribedHostPartitionSample | lemma | proof | closed | - | Simultaneous degree estimates for prescribed host capacities | BlowUpInstance, CandidacyLowerSuperRegular, CandidacySystem, HypergeometricTwoTail, InstanceLowerSuperRegular, ProductPermutationIntersectionTail, UniformSubsetIntersectionLaw |
| ProductPermutationIntersectionTail | lemma | proof | closed | - | Intersection tails for product-permutation blocks | HypergeometricTwoTail, ProductPermutationSubsetLaw, UniformSubsetIntersectionLaw |
| ProductPermutationSubsetLaw | lemma | proof | closed | - | Subset marginals of product permutations | Preamble |
| QuantitativeSuperRegularThinning | lemma | proof | closed | - | Quantitative spanning super-regular thinning | CrossEdgeRetentionCounts, IndependentEdgeSample, IndependentUnequalEdgeSampleLaw, NearEqualRetentionThreshold, PairDensity, RetentionBadEventUnion, SuperRegularPair, ThinningCountInterval, ThinningRealParameters |
| RawCandidates | definition | definition | closed | - | Raw candidates | CandidacySystem |
| RebalancingLossMargins | lemma | proof | closed | - | Floor, ceiling, and loss margins | Preamble |
| RebalancingResidualCandidacy | lemma | proof | closed | - | Residual candidacy with exceptional rows | CandidacyLowerSuperRegular, ExceptionalLeftLowerSuperRegular, UpdatedCandidacy |
| RebalancingResidualGeometry | lemma | proof | closed | - | Exact residual geometry | UpdatedCandidacy |
| RebalancingResidualHost | lemma | proof | closed | - | Residual host lower super-regularity | InstanceLowerSuperRegular, LowerSuperRegularDeletionSlicing, LowerSuperRegularPairEmbedding, PartialCompatibleEmbedding |
| RebalancingRestrictionEstimates | lemma | proof | closed | - | Estimates for the small restricted source | CandidacyLowerSuperRegular, InstanceLowerRegular, InstanceLowerSuperRegular |
| RectangleFactorCutLowerBound | lemma | proof | closed | - | Rectangle inequalities bound the cut expression | Preamble |
| ReducedSquareColoring | lemma | proof | closed | - | Proper colouring of the reduced square | Preamble |
| RefinedLowerSuperRegularTransfer | lemma | proof | closed | - | Lower super-regularity after sampling and correction | CandidacyLowerSuperRegular, InstanceLowerSuperRegular, LowerRegularRestriction |
| RegularBipartiteMatchingCount | lemma | proof | closed | - | Matching count in a regular bipartite graph | AdjacencyPermanentMatchingCount, PerfectMatching, RegularMatrixNormalization |
| RegularExtractionIneligibleArea | lemma | proof | closed | - | Area of ineligible partition rectangles | Preamble |
| RegularExtractionParameters | lemma | proof | closed | - | Uniform extraction parameters | Preamble |
| RegularExtractionPartitionGeometry | lemma | proof | closed | - | Equitable extraction geometry | Preamble, RegularExtractionIneligibleArea |
| RegularInducedMatchingUpperBound | lemma | proof | closed | - | Upper enumeration in large induced subgraphs | BregmanMatchingDegreeProduct, FactorialRootExceptionalProduct, PerfectMatching, PerfectMatchingBijectionBound, RegularPair, RegularPairUpperTail |
| RegularMatrixNormalization | lemma | proof | closed | - | - | RowProductPolynomial |
| RegularPair | definition | definition | closed | - | - | PairDensity |
| RegularPairGoodCodegrees | lemma | proof | closed | - | Good codegrees in a regular pair | SuperRegularCodegreeExceptionalBound |
| RegularPairLowerTail | lemma | proof | closed | - | Lower exceptional tail of a regular pair | FilteredProductRowCount, RegularPair |
| RegularPairUpperTail | lemma | proof | closed | - | Upper exceptional tail of a regular pair | FilteredProductRowCount, RegularPair |
| RegularSubgraph | lemma | proof | closed | - | Regular subgraph | LowerRegularPair, PairDensity, PairDensityReal, RegularExtractionParameters, RegularExtractionPartitionGeometry, RegularPair, SimultaneousUnequalRetention, WeightedRectangleExpectation |
| RegularityAfterDensityLoss | lemma | proof | closed | - | Regularity after bounded density loss | RegularPair |
| RestrictReductionEmbedding | definition | definition | closed | - | - | BlowUpReductionToAuxiliary, PartialCompatibleEmbedding |
| RestrictedDegreeVarianceBound | lemma | proof | closed | - | Variance bound from restricted degree moments | Preamble |
| RestrictedPartialEmbeddingTransport | lemma | proof | closed | - | Transport of a restricted partial law | UpdatedCandidacy, VertexSpreadRestriction |
| RestrictedRowEdgeLowerBound | lemma | proof | closed | - | Edge count after restricting the opposite part | FilteredProductRowCount |
| RestrictedSmallBlowUpInterface | lemma | proof | closed | - | Exact restricted-instance interface | CandidacySystem, InstanceLowerRegular, PartialEmbedding |
| RetentionBadEventUnion | lemma | proof | closed | - | Finite union bound on all retention tests | IndependentEdgeSample, IndependentRetentionConcentration, IndependentUnequalEdgeSampleLaw, RetentionCountControl |
| RetentionCountControl | definition | definition | closed | - | Simultaneous retention count control | IndependentRetentionCount |
| RowProductPolynomial | definition | definition | closed | - | - | Preamble |
| SaturatingSourcePair | definition | definition | closed | - | - | BlowUpInstance |
| SimpleResidualPath | definition | definition | closed | - | Simple residual source-to-sink path | FiniteIntegralFlow |
| SimultaneousGoodEdgeGraph | definition | definition | closed | - | - | SuperRegularPair |
| SimultaneousHostCandidacyRefinement | lemma | proof | closed | - | Simultaneous host and candidacy refinement | BlowUpInstance, CandidacyLowerSuperRegular, CandidacySuperRegular, CandidacySystem, CrossPairSubgraphAssembly, HostExceptionalCorrection, HostRefinementParameters, InstanceLowerSuperRegular, InstanceSuperRegular, LowerRegularPair, LowerSuperRegularPair, NearEqualSuperRegularExtraction, PairDensity, PrescribedHostPartitionSample, RefinedLowerSuperRegularTransfer, RegularPair, SuperRegularPair, SuperRegularSubgraph, TaggedCandidacyAssembly |
| SimultaneousUnequalRetention | lemma | proof | closed | - | Simultaneous unequal retention | FiniteIndependentSubgaussianTail, IndependentUnequalEdgeSampleLaw |
| SmallNeighborhoodCodegreeWindow | lemma | proof | closed | - | Small neighborhoods have no bad codegrees | Preamble |
| SourceClusterPadding | lemma | proof | closed | - | Padding source clusters to host capacity | CandidacyLowerSuperRegular, CompatibleEmbedding, CompleteRowPadding, InstanceLowerSuperRegular, PaddedSource, VertexSpreadOn, VertexSpreadRestriction |
| SpreadBlowup | theorem | proof | closed | - | Vertex-spread blow-up lemma | AuxiliarySpreadExecution, BlowUpReductionToAuxiliary, BlowupOrderMargins, ClusterRebalancing, EqualSizeParameterTable, EqualSizeTerminalConversion, RestrictReductionEmbedding, SourceClusterPadding, SupportedResidualComposition, VariableSizeInductionIteration, VertexSpreadSequential |
| SuperRegularCodegreeExceptionalBound | helper | proof | closed | - | Ordered codegree exceptions in a super-regular pair | FilteredProductRowCount, SuperRegularPair |
| SuperRegularCoreSample | lemma | proof | closed | - | Independent core thinning | FiniteIndependentSubgaussianTail, IndependentUnequalEdgeSampleLaw |
| SuperRegularErrorMonotone | lemma | proof | closed | - | Increasing the super-regularity error | SuperRegularPair |
| SuperRegularExceptionalRestoration | lemma | proof | closed | - | Exceptional-row restoration | ExceptionalCoreEdgeExtension, ExceptionalRectangleDensity, PairDensityReal, SuperRegularPair |
| SuperRegularExtractionParameters | lemma | proof | closed | - | Super-regular extraction parameters | ExtractionTailCutoffs, RegularExtractionParameters |
| SuperRegularInitialSample | lemma | proof | closed | - | Joint weighted extraction sample | FiniteIndependentSubgaussianTail, IndependentUnequalEdgeSampleLaw, RegularExtractionPartitionGeometry, WeightedRectangleExpectation |
| SuperRegularPair | definition | definition | closed | - | - | RegularPair |
| SuperRegularPairEmbedding | lemma | proof | closed | - | Super-regularity under a part embedding | SuperRegularPair |
| SuperRegularPairOneVertexDeletion | lemma | proof | closed | - | Deleting at most one vertex from each part | SuperRegularPair |
| SuperRegularSpanningFactor | lemma | proof | closed | - | Regular factor in a super-regular pair | BipartiteRegularFactorCriterion, RestrictedRowEdgeLowerBound, SuperRegularPair |
| SuperRegularSubgraph | lemma | proof | closed | - | Super-regular subgraph | LowerRegularPair, LowerSuperRegularPair, PairDensity, PairDensityReal, RegularPair, SuperRegularCoreSample, SuperRegularExceptionalRestoration, SuperRegularExtractionParameters, SuperRegularInitialSample, SuperRegularPair, SuperRegularTypicalCore |
| SuperRegularTypicalCore | lemma | proof | closed | - | Typical-row core estimates | Preamble |
| SupportedResidualComposition | lemma | proof | closed | - | - | UpdatedCandidacy, VertexSpreadSequential |
| TaggedCandidacyAssembly | lemma | proof | closed | - | Assembly of tagged candidacy extractions | CandidacySuperRegular, SuperRegularPairEmbedding |
| ThinningCountInterval | lemma | proof | closed | - | Deterministic count error transfer | Preamble |
| ThinningRealParameters | lemma | proof | closed | - | Finite scalar normalization for thinning | Preamble |
| UniformMatchingHypergeometricComparison | lemma | proof | closed | - | Uniform matching fibers versus hypergeometric masses | FourRectangleFactorialCancellation, FourRectangleMatchingFiberBound, FourRectangleSmallOrderProduct, HypergeometricMass, MatchingConcentrationCorrection, MatchingEnumeration, PerfectMatchingBijectionBound, RegularInducedMatchingUpperBound, UniformPerfectMatching |
| UniformMatchingSetImageConcentration | lemma | proof | closed | - | Uniform matching set-image concentration | HypergeometricTwoTail, MatchingConcentrationCorrectionAbsorption, MatchingEnumeration, RegularInducedMatchingUpperBound, UniformMatchingHypergeometricComparison, UniformPerfectMatching |
| UniformPerfectMatching | definition | definition | closed | - | - | PerfectMatching |
| UniformPerfectMatchingSpread | lemma | proof | closed | - | Uniform perfect matchings are spread | MatchingManyEdges, MatchingSwitching, UniformPerfectMatching, VertexSpreadOn |
| UniformSubsetIntersectionLaw | lemma | proof | closed | - | The uniform subset intersection law | HypergeometricMass |
| UpdatedCandidacy | definition | definition | closed | - | - | PartialCompatibleEmbedding |
| UpdatedCandidacyCluster | definition | definition | closed | - | - | UpdatedCandidacy |
| UpdatedCandidacyCongruence | lemma | proof | closed | - | Unused stored values do not change updated candidacy | UpdatedCandidacy |
| UpdatedCandidacyNonneighborExtension | lemma | proof | closed | - | Non-neighbour candidacy is unchanged | UpdatedCandidacyCluster |
| VariableSizeInductionBase | lemma | proof | closed | - | Initial colour-round law | CandidacySuperRegular, ColourRoundInvariant |
| VariableSizeInductionIteration | lemma | proof | closed | - | Finite execution of the colour-round induction | ColourClassSequentialCompletion, ColourRoundReset, ReducedSquareColoring, VariableSizeInductionBase, VariableSizeInductionStep |
| VariableSizeInductionStep | lemma | proof | closed | - | One-colour-class matching extension | ColourRoundInvariant, ColourRoundKernelAssembly, ColourRoundMatchingPreparation, DegreeCodegreeRegularityCriterion, ExtendUpdatedPartialEmbedding, FutureExtraVertexStability, InductionApplicationCertificate, InstanceSuperRegular, MatchingInducedLeftRowDeletion, MatchingInducedUpdatedCandidacyTransport, NearEqualFourGraphs, NearEqualVaryingGoodEdgeSuperRegularity, OneClusterExtension, ReducedSquareColoring, RegularPairGoodCodegrees, SaturatingSourcePair, VertexSpreadConditioning, VertexSpreadMonotone, VertexSpreadSequential |
| VertexSpreadConditioning | lemma | proof | closed | - | - | VertexSpreadOn |
| VertexSpreadMonotone | lemma | proof | closed | - | - | VertexSpreadOn |
| VertexSpreadOn | definition | definition | closed | - | - | CylinderEvent |
| VertexSpreadRestriction | lemma | proof | closed | - | - | VertexSpreadOn |
| VertexSpreadSequential | lemma | proof | closed | - | - | VertexSpreadOn |
| WeightedRectangleExpectation | lemma | proof | closed | - | Weighted rectangle expectation | Preamble |
| WeightedSubsetIntersectionSum | lemma | proof | closed | - | Weighted subset count by marked intersection | Preamble |

**Total:** 218 nodes | **Closed:** 218 | **Open:** 0
