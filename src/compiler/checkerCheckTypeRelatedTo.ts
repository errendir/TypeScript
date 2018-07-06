/// <reference path="moduleNameResolver.ts"/>
/// <reference path="binder.ts"/>
/// <reference path="symbolWalker.ts" />

namespace ts {
    /**
     * Checks if 'source' is related to 'target' (e.g.: is a assignable to).
     * @param source The left-hand-side of the relation.
     * @param target The right-hand-side of the relation.
     * @param relation The relation considered. One of 'identityRelation', 'subtypeRelation', 'assignableRelation', or 'comparableRelation'.
     * Used as both to determine which checks are performed and as a cache of previously computed results.
     * @param errorNode The suggested node upon which all errors will be reported, if defined. This may or may not be the actual node used.
     * @param headMessage If the error chain should be prepended by a head message, then headMessage will be used.
     * @param containingMessageChain A chain of errors to prepend any new errors found.
     */
    function checkTypeRelatedTo(
        source: Type,
        target: Type,
        relation: Map<RelationComparisonResult>,
        errorNode: Node,
        headMessage?: DiagnosticMessage,
        containingMessageChain?: DiagnosticMessageChain): boolean {

        let errorInfo: DiagnosticMessageChain;
        let maybeKeys: string[];
        let sourceStack: Type[];
        let targetStack: Type[];
        let maybeCount = 0;
        let depth = 0;
        const enum ExpandingFlags {
            None = 0,
            Source = 1,
            Target = 1 << 1,
            Both = Source | Target,
        }
        let expandingFlags = ExpandingFlags.None;
        let overflow = false;
        let isIntersectionConstituent = false;

        Debug.assert(relation !== identityRelation || !errorNode, "no error reporting in identity checking");

        const result = isRelatedTo(source, target, /*reportErrors*/ !!errorNode, headMessage);
        if (overflow) {
            error(errorNode, Diagnostics.Excessive_stack_depth_comparing_types_0_and_1, typeToString(source), typeToString(target));
        }
        else if (errorInfo) {
            if (containingMessageChain) {
                errorInfo = concatenateDiagnosticMessageChains(containingMessageChain, errorInfo);
            }

            diagnostics.add(createDiagnosticForNodeFromMessageChain(errorNode, errorInfo));
        }
        return result !== Ternary.False;

        function reportError(message: DiagnosticMessage, arg0?: string, arg1?: string, arg2?: string): void {
            Debug.assert(!!errorNode);
            errorInfo = chainDiagnosticMessages(errorInfo, message, arg0, arg1, arg2);
        }

        function reportRelationError(message: DiagnosticMessage, source: Type, target: Type) {
            let sourceType = typeToString(source);
            let targetType = typeToString(target);
            if (sourceType === targetType) {
                sourceType = typeToString(source, /*enclosingDeclaration*/ undefined, TypeFormatFlags.UseFullyQualifiedType);
                targetType = typeToString(target, /*enclosingDeclaration*/ undefined, TypeFormatFlags.UseFullyQualifiedType);
            }

            if (!message) {
                if (relation === comparableRelation) {
                    message = Diagnostics.Type_0_is_not_comparable_to_type_1;
                }
                else if (sourceType === targetType) {
                    message = Diagnostics.Type_0_is_not_assignable_to_type_1_Two_different_types_with_this_name_exist_but_they_are_unrelated;
                }
                else {
                    message = Diagnostics.Type_0_is_not_assignable_to_type_1;
                }
            }

            reportError(message, sourceType, targetType);
        }

        function tryElaborateErrorsForPrimitivesAndObjects(source: Type, target: Type) {
            const sourceType = typeToString(source);
            const targetType = typeToString(target);

            if ((globalStringType === source && stringType === target) ||
                (globalNumberType === source && numberType === target) ||
                (globalBooleanType === source && booleanType === target) ||
                (getGlobalESSymbolType(/*reportErrors*/ false) === source && esSymbolType === target)) {
                reportError(Diagnostics._0_is_a_primitive_but_1_is_a_wrapper_object_Prefer_using_0_when_possible, targetType, sourceType);
            }
        }

        function isUnionOrIntersectionTypeWithoutNullableConstituents(type: Type): boolean {
            if (!(type.flags & TypeFlags.UnionOrIntersection)) {
                return false;
            }
            // at this point we know that this is union or intersection type possibly with nullable constituents.
            // check if we still will have compound type if we ignore nullable components.
            let seenNonNullable = false;
            for (const t of (<UnionOrIntersectionType>type).types) {
                if (t.flags & TypeFlags.Nullable) {
                    continue;
                }
                if (seenNonNullable) {
                    return true;
                }
                seenNonNullable = true;
            }
            return false;
        }

        /**
         * Compare two types and return
         * * Ternary.True if they are related with no assumptions,
         * * Ternary.Maybe if they are related with assumptions of other relationships, or
         * * Ternary.False if they are not related.
         */
        function isRelatedTo(source: Type, target: Type, reportErrors?: boolean, headMessage?: DiagnosticMessage): Ternary {
            if (source.flags & TypeFlags.StringOrNumberLiteral && source.flags & TypeFlags.FreshLiteral) {
                source = (<LiteralType>source).regularType;
            }
            if (target.flags & TypeFlags.StringOrNumberLiteral && target.flags & TypeFlags.FreshLiteral) {
                target = (<LiteralType>target).regularType;
            }
            // both types are the same - covers 'they are the same primitive type or both are Any' or the same type parameter cases
            if (source === target) return Ternary.True;

            if (relation === identityRelation) {
                return isIdenticalTo(source, target);
            }

            if (isSimpleTypeRelatedTo(source, target, relation, reportErrors ? reportError : undefined)) return Ternary.True;

            if (getObjectFlags(source) & ObjectFlags.ObjectLiteral && source.flags & TypeFlags.FreshLiteral) {
                if (hasExcessProperties(<FreshObjectLiteralType>source, target, reportErrors)) {
                    if (reportErrors) {
                        reportRelationError(headMessage, source, target);
                    }
                    return Ternary.False;
                }
                // Above we check for excess properties with respect to the entire target type. When union
                // and intersection types are further deconstructed on the target side, we don't want to
                // make the check again (as it might fail for a partial target type). Therefore we obtain
                // the regular source type and proceed with that.
                if (isUnionOrIntersectionTypeWithoutNullableConstituents(target)) {
                    source = getRegularTypeOfObjectLiteral(source);
                }
            }

            if (relation !== comparableRelation &&
                !(source.flags & TypeFlags.UnionOrIntersection) &&
                !(target.flags & TypeFlags.Union) &&
                !isIntersectionConstituent &&
                source !== globalObjectType &&
                (getPropertiesOfType(source).length > 0 ||
                    getSignaturesOfType(source, SignatureKind.Call).length > 0 ||
                    getSignaturesOfType(source, SignatureKind.Construct).length > 0) &&
                isWeakType(target) &&
                !hasCommonProperties(source, target)) {
                if (reportErrors) {
                    const calls = getSignaturesOfType(source, SignatureKind.Call);
                    const constructs = getSignaturesOfType(source, SignatureKind.Construct);
                    if (calls.length > 0 && isRelatedTo(getReturnTypeOfSignature(calls[0]), target, /*reportErrors*/ false) ||
                        constructs.length > 0 && isRelatedTo(getReturnTypeOfSignature(constructs[0]), target, /*reportErrors*/ false)) {
                        reportError(Diagnostics.Value_of_type_0_has_no_properties_in_common_with_type_1_Did_you_mean_to_call_it, typeToString(source), typeToString(target));
                    }
                    else {
                        reportError(Diagnostics.Type_0_has_no_properties_in_common_with_type_1, typeToString(source), typeToString(target));
                    }
                }
                return Ternary.False;
            }

            let result = Ternary.False;
            const saveErrorInfo = errorInfo;
            const saveIsIntersectionConstituent = isIntersectionConstituent;
            isIntersectionConstituent = false;

            // Note that these checks are specifically ordered to produce correct results. In particular,
            // we need to deconstruct unions before intersections (because unions are always at the top),
            // and we need to handle "each" relations before "some" relations for the same kind of type.
            if (source.flags & TypeFlags.Union) {
                result = relation === comparableRelation ?
                    someTypeRelatedToType(source as UnionType, target, reportErrors && !(source.flags & TypeFlags.Primitive)) :
                    eachTypeRelatedToType(source as UnionType, target, reportErrors && !(source.flags & TypeFlags.Primitive));
            }
            else {
                if (target.flags & TypeFlags.Union) {
                    result = typeRelatedToSomeType(source, <UnionType>target, reportErrors && !(source.flags & TypeFlags.Primitive) && !(target.flags & TypeFlags.Primitive));
                }
                else if (target.flags & TypeFlags.Intersection) {
                    isIntersectionConstituent = true;
                    result = typeRelatedToEachType(source, target as IntersectionType, reportErrors);
                }
                else if (source.flags & TypeFlags.Intersection) {
                    // Check to see if any constituents of the intersection are immediately related to the target.
                    //
                    // Don't report errors though. Checking whether a constituent is related to the source is not actually
                    // useful and leads to some confusing error messages. Instead it is better to let the below checks
                    // take care of this, or to not elaborate at all. For instance,
                    //
                    //    - For an object type (such as 'C = A & B'), users are usually more interested in structural errors.
                    //
                    //    - For a union type (such as '(A | B) = (C & D)'), it's better to hold onto the whole intersection
                    //          than to report that 'D' is not assignable to 'A' or 'B'.
                    //
                    //    - For a primitive type or type parameter (such as 'number = A & B') there is no point in
                    //          breaking the intersection apart.
                    result = someTypeRelatedToType(<IntersectionType>source, target, /*reportErrors*/ false);
                }
                if (!result && (source.flags & TypeFlags.StructuredOrTypeVariable || target.flags & TypeFlags.StructuredOrTypeVariable)) {
                    if (result = recursiveTypeRelatedTo(source, target, reportErrors)) {
                        errorInfo = saveErrorInfo;
                    }
                }
            }

            isIntersectionConstituent = saveIsIntersectionConstituent;

            if (!result && reportErrors) {
                if (source.flags & TypeFlags.Object && target.flags & TypeFlags.Primitive) {
                    tryElaborateErrorsForPrimitivesAndObjects(source, target);
                }
                else if (source.symbol && source.flags & TypeFlags.Object && globalObjectType === source) {
                    reportError(Diagnostics.The_Object_type_is_assignable_to_very_few_other_types_Did_you_mean_to_use_the_any_type_instead);
                }
                reportRelationError(headMessage, source, target);
            }
            return result;
        }

        function isIdenticalTo(source: Type, target: Type): Ternary {
            let result: Ternary;
            if (source.flags & TypeFlags.Object && target.flags & TypeFlags.Object) {
                return recursiveTypeRelatedTo(source, target, /*reportErrors*/ false);
            }
            if (source.flags & TypeFlags.Union && target.flags & TypeFlags.Union ||
                source.flags & TypeFlags.Intersection && target.flags & TypeFlags.Intersection) {
                if (result = eachTypeRelatedToSomeType(<UnionOrIntersectionType>source, <UnionOrIntersectionType>target)) {
                    if (result &= eachTypeRelatedToSomeType(<UnionOrIntersectionType>target, <UnionOrIntersectionType>source)) {
                        return result;
                    }
                }
            }
            return Ternary.False;
        }

        function hasExcessProperties(source: FreshObjectLiteralType, target: Type, reportErrors: boolean): boolean {
            if (maybeTypeOfKind(target, TypeFlags.Object) && !(getObjectFlags(target) & ObjectFlags.ObjectLiteralPatternWithComputedProperties)) {
                const isComparingJsxAttributes = !!(source.flags & TypeFlags.JsxAttributes);
                if ((relation === assignableRelation || relation === comparableRelation) &&
                    (isTypeSubsetOf(globalObjectType, target) || (!isComparingJsxAttributes && isEmptyObjectType(target)))) {
                    return false;
                }
                if (target.flags & TypeFlags.Union) {
                    const discriminantType = findMatchingDiscriminantType(source, target as UnionType);
                    if (discriminantType)  {
                        // check excess properties against discriminant type only, not the entire union
                        return hasExcessProperties(source, discriminantType, reportErrors);
                    }
                }
                for (const prop of getPropertiesOfObjectType(source)) {
                    if (!isKnownProperty(target, prop.escapedName, isComparingJsxAttributes)) {
                        if (reportErrors) {
                            // We know *exactly* where things went wrong when comparing the types.
                            // Use this property as the error node as this will be more helpful in
                            // reasoning about what went wrong.
                            Debug.assert(!!errorNode);
                            if (isJsxAttributes(errorNode) || isJsxOpeningLikeElement(errorNode)) {
                                // JsxAttributes has an object-literal flag and undergo same type-assignablity check as normal object-literal.
                                // However, using an object-literal error message will be very confusing to the users so we give different a message.
                                reportError(Diagnostics.Property_0_does_not_exist_on_type_1, symbolToString(prop), typeToString(target));
                            }
                            else {
                                // use the property's value declaration if the property is assigned inside the literal itself
                                const objectLiteralDeclaration = source.symbol && firstOrUndefined(source.symbol.declarations);
                                let suggestion;
                                if (prop.valueDeclaration && findAncestor(prop.valueDeclaration, d => d === objectLiteralDeclaration)) {
                                    const propDeclaration = prop.valueDeclaration as ObjectLiteralElementLike;
                                    Debug.assertNode(propDeclaration, isObjectLiteralElementLike);

                                    errorNode = propDeclaration;

                                    if (isIdentifier(propDeclaration.name)) {
                                        suggestion = getSuggestionForNonexistentProperty(propDeclaration.name, target);
                                    }
                                }

                                if (suggestion !== undefined) {
                                    reportError(Diagnostics.Object_literal_may_only_specify_known_properties_but_0_does_not_exist_in_type_1_Did_you_mean_to_write_2,
                                        symbolToString(prop), typeToString(target), suggestion);
                                }
                                else {
                                    reportError(Diagnostics.Object_literal_may_only_specify_known_properties_and_0_does_not_exist_in_type_1,
                                        symbolToString(prop), typeToString(target));
                                }
                            }
                        }
                        return true;
                    }
                }
            }
            return false;
        }

        function eachTypeRelatedToSomeType(source: UnionOrIntersectionType, target: UnionOrIntersectionType): Ternary {
            let result = Ternary.True;
            const sourceTypes = source.types;
            for (const sourceType of sourceTypes) {
                const related = typeRelatedToSomeType(sourceType, target, /*reportErrors*/ false);
                if (!related) {
                    return Ternary.False;
                }
                result &= related;
            }
            return result;
        }

        function typeRelatedToSomeType(source: Type, target: UnionOrIntersectionType, reportErrors: boolean): Ternary {
            const targetTypes = target.types;
            if (target.flags & TypeFlags.Union && containsType(targetTypes, source)) {
                return Ternary.True;
            }
            for (const type of targetTypes) {
                const related = isRelatedTo(source, type, /*reportErrors*/ false);
                if (related) {
                    return related;
                }
            }
            if (reportErrors) {
                const discriminantType = findMatchingDiscriminantType(source, target);
                isRelatedTo(source, discriminantType || targetTypes[targetTypes.length - 1], /*reportErrors*/ true);
            }
            return Ternary.False;
        }

        function findMatchingDiscriminantType(source: Type, target: UnionOrIntersectionType) {
            let match: Type;
            const sourceProperties = getPropertiesOfObjectType(source);
            if (sourceProperties) {
                const sourceProperty = findSingleDiscriminantProperty(sourceProperties, target);
                if (sourceProperty) {
                    const sourceType = getTypeOfSymbol(sourceProperty);
                    for (const type of target.types) {
                        const targetType = getTypeOfPropertyOfType(type, sourceProperty.escapedName);
                        if (targetType && isRelatedTo(sourceType, targetType)) {
                            if (match) {
                                return undefined;
                            }
                            match = type;
                        }
                    }
                }
            }
            return match;
        }

        function typeRelatedToEachType(source: Type, target: IntersectionType, reportErrors: boolean): Ternary {
            let result = Ternary.True;
            const targetTypes = target.types;
            for (const targetType of targetTypes) {
                const related = isRelatedTo(source, targetType, reportErrors);
                if (!related) {
                    return Ternary.False;
                }
                result &= related;
            }
            return result;
        }

        function someTypeRelatedToType(source: UnionOrIntersectionType, target: Type, reportErrors: boolean): Ternary {
            const sourceTypes = source.types;
            if (source.flags & TypeFlags.Union && containsType(sourceTypes, target)) {
                return Ternary.True;
            }
            const len = sourceTypes.length;
            for (let i = 0; i < len; i++) {
                const related = isRelatedTo(sourceTypes[i], target, reportErrors && i === len - 1);
                if (related) {
                    return related;
                }
            }
            return Ternary.False;
        }

        function eachTypeRelatedToType(source: UnionOrIntersectionType, target: Type, reportErrors: boolean): Ternary {
            let result = Ternary.True;
            const sourceTypes = source.types;
            for (const sourceType of sourceTypes) {
                const related = isRelatedTo(sourceType, target, reportErrors);
                if (!related) {
                    return Ternary.False;
                }
                result &= related;
            }
            return result;
        }

        function typeArgumentsRelatedTo(source: TypeReference, target: TypeReference, variances: Variance[], reportErrors: boolean): Ternary {
            const sources = source.typeArguments || emptyArray;
            const targets = target.typeArguments || emptyArray;
            if (sources.length !== targets.length && relation === identityRelation) {
                return Ternary.False;
            }
            const length = sources.length <= targets.length ? sources.length : targets.length;
            let result = Ternary.True;
            for (let i = 0; i < length; i++) {
                // When variance information isn't available we default to covariance. This happens
                // in the process of computing variance information for recursive types and when
                // comparing 'this' type arguments.
                const variance = i < variances.length ? variances[i] : Variance.Covariant;
                // We ignore arguments for independent type parameters (because they're never witnessed).
                if (variance !== Variance.Independent) {
                    const s = sources[i];
                    const t = targets[i];
                    let related = Ternary.True;
                    if (variance === Variance.Covariant) {
                        related = isRelatedTo(s, t, reportErrors);
                    }
                    else if (variance === Variance.Contravariant) {
                        related = isRelatedTo(t, s, reportErrors);
                    }
                    else if (variance === Variance.Bivariant) {
                        // In the bivariant case we first compare contravariantly without reporting
                        // errors. Then, if that doesn't succeed, we compare covariantly with error
                        // reporting. Thus, error elaboration will be based on the the covariant check,
                        // which is generally easier to reason about.
                        related = isRelatedTo(t, s, /*reportErrors*/ false);
                        if (!related) {
                            related = isRelatedTo(s, t, reportErrors);
                        }
                    }
                    else {
                        // In the invariant case we first compare covariantly, and only when that
                        // succeeds do we proceed to compare contravariantly. Thus, error elaboration
                        // will typically be based on the covariant check.
                        related = isRelatedTo(s, t, reportErrors);
                        if (related) {
                            related &= isRelatedTo(t, s, reportErrors);
                        }
                    }
                    if (!related) {
                        return Ternary.False;
                    }
                    result &= related;
                }
            }
            return result;
        }

        // Determine if possibly recursive types are related. First, check if the result is already available in the global cache.
        // Second, check if we have already started a comparison of the given two types in which case we assume the result to be true.
        // Third, check if both types are part of deeply nested chains of generic type instantiations and if so assume the types are
        // equal and infinitely expanding. Fourth, if we have reached a depth of 100 nested comparisons, assume we have runaway recursion
        // and issue an error. Otherwise, actually compare the structure of the two types.
        function recursiveTypeRelatedTo(source: Type, target: Type, reportErrors: boolean): Ternary {
            if (overflow) {
                return Ternary.False;
            }
            const id = getRelationKey(source, target, relation);
            const related = relation.get(id);
            if (related !== undefined) {
                if (reportErrors && related === RelationComparisonResult.Failed) {
                    // We are elaborating errors and the cached result is an unreported failure. Record the result as a reported
                    // failure and continue computing the relation such that errors get reported.
                    relation.set(id, RelationComparisonResult.FailedAndReported);
                }
                else {
                    return related === RelationComparisonResult.Succeeded ? Ternary.True : Ternary.False;
                }
            }
            if (!maybeKeys) {
                maybeKeys = [];
                sourceStack = [];
                targetStack = [];
            }
            else {
                for (let i = 0; i < maybeCount; i++) {
                    // If source and target are already being compared, consider them related with assumptions
                    if (id === maybeKeys[i]) {
                        return Ternary.Maybe;
                    }
                }
                if (depth === 100) {
                    overflow = true;
                    return Ternary.False;
                }
            }
            const maybeStart = maybeCount;
            maybeKeys[maybeCount] = id;
            maybeCount++;
            sourceStack[depth] = source;
            targetStack[depth] = target;
            depth++;
            const saveExpandingFlags = expandingFlags;
            if (!(expandingFlags & ExpandingFlags.Source) && isDeeplyNestedType(source, sourceStack, depth)) expandingFlags |= ExpandingFlags.Source;
            if (!(expandingFlags & ExpandingFlags.Target) && isDeeplyNestedType(target, targetStack, depth)) expandingFlags |= ExpandingFlags.Target;
            const result = expandingFlags !== ExpandingFlags.Both ? structuredTypeRelatedTo(source, target, reportErrors) : Ternary.Maybe;
            expandingFlags = saveExpandingFlags;
            depth--;
            if (result) {
                if (result === Ternary.True || depth === 0) {
                    // If result is definitely true, record all maybe keys as having succeeded
                    for (let i = maybeStart; i < maybeCount; i++) {
                        relation.set(maybeKeys[i], RelationComparisonResult.Succeeded);
                    }
                    maybeCount = maybeStart;
                }
            }
            else {
                // A false result goes straight into global cache (when something is false under
                // assumptions it will also be false without assumptions)
                relation.set(id, reportErrors ? RelationComparisonResult.FailedAndReported : RelationComparisonResult.Failed);
                maybeCount = maybeStart;
            }
            return result;
        }

        function structuredTypeRelatedTo(source: Type, target: Type, reportErrors: boolean): Ternary {
            let result: Ternary;
            const saveErrorInfo = errorInfo;
            if (target.flags & TypeFlags.TypeParameter) {
                // A source type { [P in keyof T]: X } is related to a target type T if X is related to T[P].
                if (getObjectFlags(source) & ObjectFlags.Mapped && getConstraintTypeFromMappedType(<MappedType>source) === getIndexType(target)) {
                    if (!(<MappedType>source).declaration.questionToken) {
                        const templateType = getTemplateTypeFromMappedType(<MappedType>source);
                        const indexedAccessType = getIndexedAccessType(target, getTypeParameterFromMappedType(<MappedType>source));
                        if (result = isRelatedTo(templateType, indexedAccessType, reportErrors)) {
                            return result;
                        }
                    }
                }
            }
            else if (target.flags & TypeFlags.Index) {
                // A keyof S is related to a keyof T if T is related to S.
                if (source.flags & TypeFlags.Index) {
                    if (result = isRelatedTo((<IndexType>target).type, (<IndexType>source).type, /*reportErrors*/ false)) {
                        return result;
                    }
                }
                // A type S is assignable to keyof T if S is assignable to keyof C, where C is the
                // constraint of T.
                const constraint = getConstraintOfType((<IndexType>target).type);
                if (constraint) {
                    if (result = isRelatedTo(source, getIndexType(constraint), reportErrors)) {
                        return result;
                    }
                }
            }
            else if (target.flags & TypeFlags.IndexedAccess) {
                // A type S is related to a type T[K] if S is related to A[K], where K is string-like and
                // A is the apparent type of S.
                const constraint = getConstraintOfIndexedAccess(<IndexedAccessType>target);
                if (constraint) {
                    if (result = isRelatedTo(source, constraint, reportErrors)) {
                        errorInfo = saveErrorInfo;
                        return result;
                    }
                }
            }

            if (source.flags & TypeFlags.TypeParameter) {
                // A source type T is related to a target type { [P in keyof T]: X } if T[P] is related to X.
                if (getObjectFlags(target) & ObjectFlags.Mapped && getConstraintTypeFromMappedType(<MappedType>target) === getIndexType(source)) {
                    const indexedAccessType = getIndexedAccessType(source, getTypeParameterFromMappedType(<MappedType>target));
                    const templateType = getTemplateTypeFromMappedType(<MappedType>target);
                    if (result = isRelatedTo(indexedAccessType, templateType, reportErrors)) {
                        errorInfo = saveErrorInfo;
                        return result;
                    }
                }
                else {
                    let constraint = getConstraintOfTypeParameter(<TypeParameter>source);
                    // A type parameter with no constraint is not related to the non-primitive object type.
                    if (constraint || !(target.flags & TypeFlags.NonPrimitive)) {
                        if (!constraint || constraint.flags & TypeFlags.Any) {
                            constraint = emptyObjectType;
                        }
                        // Report constraint errors only if the constraint is not the empty object type
                        const reportConstraintErrors = reportErrors && constraint !== emptyObjectType;
                        if (result = isRelatedTo(constraint, target, reportConstraintErrors)) {
                            errorInfo = saveErrorInfo;
                            return result;
                        }
                    }
                }
            }
            else if (source.flags & TypeFlags.IndexedAccess) {
                // A type S[K] is related to a type T if A[K] is related to T, where K is string-like and
                // A is the apparent type of S.
                const constraint = getConstraintOfIndexedAccess(<IndexedAccessType>source);
                if (constraint) {
                    if (result = isRelatedTo(constraint, target, reportErrors)) {
                        errorInfo = saveErrorInfo;
                        return result;
                    }
                }
                else if (target.flags & TypeFlags.IndexedAccess && (<IndexedAccessType>source).indexType === (<IndexedAccessType>target).indexType) {
                    // if we have indexed access types with identical index types, see if relationship holds for
                    // the two object types.
                    if (result = isRelatedTo((<IndexedAccessType>source).objectType, (<IndexedAccessType>target).objectType, reportErrors)) {
                        return result;
                    }
                }
            }
            else {
                if (getObjectFlags(source) & ObjectFlags.Reference && getObjectFlags(target) & ObjectFlags.Reference && (<TypeReference>source).target === (<TypeReference>target).target &&
                    !(source.flags & TypeFlags.MarkerType || target.flags & TypeFlags.MarkerType)) {
                    // We have type references to the same generic type, and the type references are not marker
                    // type references (which are intended by be compared structurally). Obtain the variance
                    // information for the type parameters and relate the type arguments accordingly.
                    const variances = getVariances((<TypeReference>source).target);
                    if (result = typeArgumentsRelatedTo(<TypeReference>source, <TypeReference>target, variances, reportErrors)) {
                        return result;
                    }
                    // The type arguments did not relate appropriately, but it may be because we have no variance
                    // information (in which case typeArgumentsRelatedTo defaulted to covariance for all type
                    // arguments). It might also be the case that the target type has a 'void' type argument for
                    // a covariant type parameter that is only used in return positions within the generic type
                    // (in which case any type argument is permitted on the source side). In those cases we proceed
                    // with a structural comparison. Otherwise, we know for certain the instantiations aren't
                    // related and we can return here.
                    if (variances !== emptyArray && !hasCovariantVoidArgument(<TypeReference>target, variances)) {
                        // In some cases generic types that are covariant in regular type checking mode become
                        // invariant in --strictFunctionTypes mode because one or more type parameters are used in
                        // both co- and contravariant positions. In order to make it easier to diagnose *why* such
                        // types are invariant, if any of the type parameters are invariant we reset the reported
                        // errors and instead force a structural comparison (which will include elaborations that
                        // reveal the reason).
                        if (!(reportErrors && some(variances, v => v === Variance.Invariant))) {
                            return Ternary.False;
                        }
                        errorInfo = saveErrorInfo;
                    }
                }
                // Even if relationship doesn't hold for unions, intersections, or generic type references,
                // it may hold in a structural comparison.
                const sourceIsPrimitive = !!(source.flags & TypeFlags.Primitive);
                if (relation !== identityRelation) {
                    source = getApparentType(source);
                }
                // In a check of the form X = A & B, we will have previously checked if A relates to X or B relates
                // to X. Failing both of those we want to check if the aggregation of A and B's members structurally
                // relates to X. Thus, we include intersection types on the source side here.
                if (source.flags & (TypeFlags.Object | TypeFlags.Intersection) && target.flags & TypeFlags.Object) {
                    // Report structural errors only if we haven't reported any errors yet
                    const reportStructuralErrors = reportErrors && errorInfo === saveErrorInfo && !sourceIsPrimitive;
                    // An empty object type is related to any mapped type that includes a '?' modifier.
                    if (isPartialMappedType(target) && !isGenericMappedType(source) && isEmptyObjectType(source)) {
                        result = Ternary.True;
                    }
                    else if (isGenericMappedType(target)) {
                        result = isGenericMappedType(source) ? mappedTypeRelatedTo(<MappedType>source, <MappedType>target, reportStructuralErrors) : Ternary.False;
                    }
                    else {
                        result = propertiesRelatedTo(source, target, reportStructuralErrors);
                        if (result) {
                            result &= signaturesRelatedTo(source, target, SignatureKind.Call, reportStructuralErrors);
                            if (result) {
                                result &= signaturesRelatedTo(source, target, SignatureKind.Construct, reportStructuralErrors);
                                if (result) {
                                    result &= indexTypesRelatedTo(source, target, IndexKind.String, sourceIsPrimitive, reportStructuralErrors);
                                    if (result) {
                                        result &= indexTypesRelatedTo(source, target, IndexKind.Number, sourceIsPrimitive, reportStructuralErrors);
                                    }
                                }
                            }
                        }
                    }
                    if (result) {
                        errorInfo = saveErrorInfo;
                        return result;
                    }
                }
            }
            return Ternary.False;
        }

        // A type [P in S]: X is related to a type [Q in T]: Y if T is related to S and X' is
        // related to Y, where X' is an instantiation of X in which P is replaced with Q. Notice
        // that S and T are contra-variant whereas X and Y are co-variant.
        function mappedTypeRelatedTo(source: MappedType, target: MappedType, reportErrors: boolean): Ternary {
            const sourceReadonly = !!source.declaration.readonlyToken;
            const sourceOptional = !!source.declaration.questionToken;
            const targetReadonly = !!target.declaration.readonlyToken;
            const targetOptional = !!target.declaration.questionToken;
            const modifiersRelated = relation === identityRelation ?
                sourceReadonly === targetReadonly && sourceOptional === targetOptional :
                relation === comparableRelation || !sourceOptional || targetOptional;
            if (modifiersRelated) {
                let result: Ternary;
                if (result = isRelatedTo(getConstraintTypeFromMappedType(<MappedType>target), getConstraintTypeFromMappedType(<MappedType>source), reportErrors)) {
                    const mapper = createTypeMapper([getTypeParameterFromMappedType(<MappedType>source)], [getTypeParameterFromMappedType(<MappedType>target)]);
                    return result & isRelatedTo(instantiateType(getTemplateTypeFromMappedType(<MappedType>source), mapper), getTemplateTypeFromMappedType(<MappedType>target), reportErrors);
                }
            }
            return Ternary.False;
        }

        function propertiesRelatedTo(source: Type, target: Type, reportErrors: boolean): Ternary {
            if (relation === identityRelation) {
                return propertiesIdenticalTo(source, target);
            }
            const requireOptionalProperties = relation === subtypeRelation && !(getObjectFlags(source) & ObjectFlags.ObjectLiteral);
            const unmatchedProperty = getUnmatchedProperty(source, target, requireOptionalProperties);
            if (unmatchedProperty) {
                if (reportErrors) {
                    reportError(Diagnostics.Property_0_is_missing_in_type_1, symbolToString(unmatchedProperty), typeToString(source));
                }
                return Ternary.False;
            }
            let result = Ternary.True;
            const properties = getPropertiesOfObjectType(target);
            for (const targetProp of properties) {
                if (!(targetProp.flags & SymbolFlags.Prototype)) {
                    const sourceProp = getPropertyOfType(source, targetProp.escapedName);
                    if (sourceProp && sourceProp !== targetProp) {
                        const sourcePropFlags = getDeclarationModifierFlagsFromSymbol(sourceProp);
                        const targetPropFlags = getDeclarationModifierFlagsFromSymbol(targetProp);
                        if (sourcePropFlags & ModifierFlags.Private || targetPropFlags & ModifierFlags.Private) {
                            if (getCheckFlags(sourceProp) & CheckFlags.ContainsPrivate) {
                                if (reportErrors) {
                                    reportError(Diagnostics.Property_0_has_conflicting_declarations_and_is_inaccessible_in_type_1, symbolToString(sourceProp), typeToString(source));
                                }
                                return Ternary.False;
                            }
                            if (sourceProp.valueDeclaration !== targetProp.valueDeclaration) {
                                if (reportErrors) {
                                    if (sourcePropFlags & ModifierFlags.Private && targetPropFlags & ModifierFlags.Private) {
                                        reportError(Diagnostics.Types_have_separate_declarations_of_a_private_property_0, symbolToString(targetProp));
                                    }
                                    else {
                                        reportError(Diagnostics.Property_0_is_private_in_type_1_but_not_in_type_2, symbolToString(targetProp),
                                            typeToString(sourcePropFlags & ModifierFlags.Private ? source : target),
                                            typeToString(sourcePropFlags & ModifierFlags.Private ? target : source));
                                    }
                                }
                                return Ternary.False;
                            }
                        }
                        else if (targetPropFlags & ModifierFlags.Protected) {
                            if (!isValidOverrideOf(sourceProp, targetProp)) {
                                if (reportErrors) {
                                    reportError(Diagnostics.Property_0_is_protected_but_type_1_is_not_a_class_derived_from_2, symbolToString(targetProp),
                                        typeToString(getDeclaringClass(sourceProp) || source), typeToString(getDeclaringClass(targetProp) || target));
                                }
                                return Ternary.False;
                            }
                        }
                        else if (sourcePropFlags & ModifierFlags.Protected) {
                            if (reportErrors) {
                                reportError(Diagnostics.Property_0_is_protected_in_type_1_but_public_in_type_2,
                                    symbolToString(targetProp), typeToString(source), typeToString(target));
                            }
                            return Ternary.False;
                        }
                        const related = isRelatedTo(getTypeOfSymbol(sourceProp), getTypeOfSymbol(targetProp), reportErrors);
                        if (!related) {
                            if (reportErrors) {
                                reportError(Diagnostics.Types_of_property_0_are_incompatible, symbolToString(targetProp));
                            }
                            return Ternary.False;
                        }
                        result &= related;
                        // When checking for comparability, be more lenient with optional properties.
                        if (relation !== comparableRelation && sourceProp.flags & SymbolFlags.Optional && !(targetProp.flags & SymbolFlags.Optional)) {
                            // TypeScript 1.0 spec (April 2014): 3.8.3
                            // S is a subtype of a type T, and T is a supertype of S if ...
                            // S' and T are object types and, for each member M in T..
                            // M is a property and S' contains a property N where
                            // if M is a required property, N is also a required property
                            // (M - property in T)
                            // (N - property in S)
                            if (reportErrors) {
                                reportError(Diagnostics.Property_0_is_optional_in_type_1_but_required_in_type_2,
                                    symbolToString(targetProp), typeToString(source), typeToString(target));
                            }
                            return Ternary.False;
                        }
                    }
                }
            }
            return result;
        }

        /**
         * A type is 'weak' if it is an object type with at least one optional property
         * and no required properties, call/construct signatures or index signatures
         */
        function isWeakType(type: Type): boolean {
            if (type.flags & TypeFlags.Object) {
                const resolved = resolveStructuredTypeMembers(<ObjectType>type);
                return resolved.callSignatures.length === 0 && resolved.constructSignatures.length === 0 &&
                    !resolved.stringIndexInfo && !resolved.numberIndexInfo &&
                    resolved.properties.length > 0 &&
                    every(resolved.properties, p => !!(p.flags & SymbolFlags.Optional));
            }
            if (type.flags & TypeFlags.Intersection) {
                return every((<IntersectionType>type).types, isWeakType);
            }
            return false;
        }

        function hasCommonProperties(source: Type, target: Type) {
            const isComparingJsxAttributes = !!(source.flags & TypeFlags.JsxAttributes);
            for (const prop of getPropertiesOfType(source)) {
                if (isKnownProperty(target, prop.escapedName, isComparingJsxAttributes)) {
                    return true;
                }
            }
            return false;
        }

        function propertiesIdenticalTo(source: Type, target: Type): Ternary {
            if (!(source.flags & TypeFlags.Object && target.flags & TypeFlags.Object)) {
                return Ternary.False;
            }
            const sourceProperties = getPropertiesOfObjectType(source);
            const targetProperties = getPropertiesOfObjectType(target);
            if (sourceProperties.length !== targetProperties.length) {
                return Ternary.False;
            }
            let result = Ternary.True;
            for (const sourceProp of sourceProperties) {
                const targetProp = getPropertyOfObjectType(target, sourceProp.escapedName);
                if (!targetProp) {
                    return Ternary.False;
                }
                const related = compareProperties(sourceProp, targetProp, isRelatedTo);
                if (!related) {
                    return Ternary.False;
                }
                result &= related;
            }
            return result;
        }

        function signaturesRelatedTo(source: Type, target: Type, kind: SignatureKind, reportErrors: boolean): Ternary {
            if (relation === identityRelation) {
                return signaturesIdenticalTo(source, target, kind);
            }
            if (target === anyFunctionType || source === anyFunctionType) {
                return Ternary.True;
            }

            const sourceSignatures = getSignaturesOfType(source, kind);
            const targetSignatures = getSignaturesOfType(target, kind);
            if (kind === SignatureKind.Construct && sourceSignatures.length && targetSignatures.length) {
                if (isAbstractConstructorType(source) && !isAbstractConstructorType(target)) {
                    // An abstract constructor type is not assignable to a non-abstract constructor type
                    // as it would otherwise be possible to new an abstract class. Note that the assignability
                    // check we perform for an extends clause excludes construct signatures from the target,
                    // so this check never proceeds.
                    if (reportErrors) {
                        reportError(Diagnostics.Cannot_assign_an_abstract_constructor_type_to_a_non_abstract_constructor_type);
                    }
                    return Ternary.False;
                }
                if (!constructorVisibilitiesAreCompatible(sourceSignatures[0], targetSignatures[0], reportErrors)) {
                    return Ternary.False;
                }
            }

            let result = Ternary.True;
            const saveErrorInfo = errorInfo;

            if (getObjectFlags(source) & ObjectFlags.Instantiated && getObjectFlags(target) & ObjectFlags.Instantiated && source.symbol === target.symbol) {
                // We have instantiations of the same anonymous type (which typically will be the type of a
                // method). Simply do a pairwise comparison of the signatures in the two signature lists instead
                // of the much more expensive N * M comparison matrix we explore below. We erase type parameters
                // as they are known to always be the same.
                for (let i = 0; i < targetSignatures.length; i++) {
                    const related = signatureRelatedTo(sourceSignatures[i], targetSignatures[i], /*erase*/ true, reportErrors);
                    if (!related) {
                        return Ternary.False;
                    }
                    result &= related;
                }
            }
            else if (sourceSignatures.length === 1 && targetSignatures.length === 1) {
                // For simple functions (functions with a single signature) we only erase type parameters for
                // the comparable relation. Otherwise, if the source signature is generic, we instantiate it
                // in the context of the target signature before checking the relationship. Ideally we'd do
                // this regardless of the number of signatures, but the potential costs are prohibitive due
                // to the quadratic nature of the logic below.
                const eraseGenerics = relation === comparableRelation || compilerOptions.noStrictGenericChecks;
                result = signatureRelatedTo(sourceSignatures[0], targetSignatures[0], eraseGenerics, reportErrors);
            }
            else {
                outer: for (const t of targetSignatures) {
                    // Only elaborate errors from the first failure
                    let shouldElaborateErrors = reportErrors;
                    for (const s of sourceSignatures) {
                        const related = signatureRelatedTo(s, t, /*erase*/ true, shouldElaborateErrors);
                        if (related) {
                            result &= related;
                            errorInfo = saveErrorInfo;
                            continue outer;
                        }
                        shouldElaborateErrors = false;
                    }

                    if (shouldElaborateErrors) {
                        reportError(Diagnostics.Type_0_provides_no_match_for_the_signature_1,
                            typeToString(source),
                            signatureToString(t, /*enclosingDeclaration*/ undefined, /*flags*/ undefined, kind));
                    }
                    return Ternary.False;
                }
            }
            return result;
        }

        /**
         * See signatureAssignableTo, compareSignaturesIdentical
         */
        function signatureRelatedTo(source: Signature, target: Signature, erase: boolean, reportErrors: boolean): Ternary {
            return compareSignaturesRelated(erase ? getErasedSignature(source) : source, erase ? getErasedSignature(target) : target,
                CallbackCheck.None, /*ignoreReturnTypes*/ false, reportErrors, reportError, isRelatedTo);
        }

        function signaturesIdenticalTo(source: Type, target: Type, kind: SignatureKind): Ternary {
            const sourceSignatures = getSignaturesOfType(source, kind);
            const targetSignatures = getSignaturesOfType(target, kind);
            if (sourceSignatures.length !== targetSignatures.length) {
                return Ternary.False;
            }
            let result = Ternary.True;
            for (let i = 0; i < sourceSignatures.length; i++) {
                const related = compareSignaturesIdentical(sourceSignatures[i], targetSignatures[i], /*partialMatch*/ false, /*ignoreThisTypes*/ false, /*ignoreReturnTypes*/ false, isRelatedTo);
                if (!related) {
                    return Ternary.False;
                }
                result &= related;
            }
            return result;
        }

        function eachPropertyRelatedTo(source: Type, target: Type, kind: IndexKind, reportErrors: boolean): Ternary {
            let result = Ternary.True;
            for (const prop of getPropertiesOfObjectType(source)) {
                if (kind === IndexKind.String || isNumericLiteralName(prop.escapedName)) {
                    const related = isRelatedTo(getTypeOfSymbol(prop), target, reportErrors);
                    if (!related) {
                        if (reportErrors) {
                            reportError(Diagnostics.Property_0_is_incompatible_with_index_signature, symbolToString(prop));
                        }
                        return Ternary.False;
                    }
                    result &= related;
                }
            }
            return result;
        }

        function indexInfoRelatedTo(sourceInfo: IndexInfo, targetInfo: IndexInfo, reportErrors: boolean) {
            const related = isRelatedTo(sourceInfo.type, targetInfo.type, reportErrors);
            if (!related && reportErrors) {
                reportError(Diagnostics.Index_signatures_are_incompatible);
            }
            return related;
        }

        function indexTypesRelatedTo(source: Type, target: Type, kind: IndexKind, sourceIsPrimitive: boolean, reportErrors: boolean) {
            if (relation === identityRelation) {
                return indexTypesIdenticalTo(source, target, kind);
            }
            const targetInfo = getIndexInfoOfType(target, kind);
            if (!targetInfo || targetInfo.type.flags & TypeFlags.Any && !sourceIsPrimitive) {
                // Index signature of type any permits assignment from everything but primitives
                return Ternary.True;
            }
            const sourceInfo = getIndexInfoOfType(source, kind) ||
                kind === IndexKind.Number && getIndexInfoOfType(source, IndexKind.String);
            if (sourceInfo) {
                return indexInfoRelatedTo(sourceInfo, targetInfo, reportErrors);
            }
            if (isGenericMappedType(source)) {
                // A generic mapped type { [P in K]: T } is related to an index signature { [x: string]: U }
                // if T is related to U.
                return kind === IndexKind.String && isRelatedTo(getTemplateTypeFromMappedType(<MappedType>source), targetInfo.type, reportErrors);
            }
            if (isObjectTypeWithInferableIndex(source)) {
                let related = Ternary.True;
                if (kind === IndexKind.String) {
                    const sourceNumberInfo = getIndexInfoOfType(source, IndexKind.Number);
                    if (sourceNumberInfo) {
                        related = indexInfoRelatedTo(sourceNumberInfo, targetInfo, reportErrors);
                    }
                }
                if (related) {
                    related &= eachPropertyRelatedTo(source, targetInfo.type, kind, reportErrors);
                }
                return related;
            }
            if (reportErrors) {
                reportError(Diagnostics.Index_signature_is_missing_in_type_0, typeToString(source));
            }
            return Ternary.False;
        }

        function indexTypesIdenticalTo(source: Type, target: Type, indexKind: IndexKind): Ternary {
            const targetInfo = getIndexInfoOfType(target, indexKind);
            const sourceInfo = getIndexInfoOfType(source, indexKind);
            if (!sourceInfo && !targetInfo) {
                return Ternary.True;
            }
            if (sourceInfo && targetInfo && sourceInfo.isReadonly === targetInfo.isReadonly) {
                return isRelatedTo(sourceInfo.type, targetInfo.type);
            }
            return Ternary.False;
        }

        function constructorVisibilitiesAreCompatible(sourceSignature: Signature, targetSignature: Signature, reportErrors: boolean) {
            if (!sourceSignature.declaration || !targetSignature.declaration) {
                return true;
            }

            const sourceAccessibility = getSelectedModifierFlags(sourceSignature.declaration, ModifierFlags.NonPublicAccessibilityModifier);
            const targetAccessibility = getSelectedModifierFlags(targetSignature.declaration, ModifierFlags.NonPublicAccessibilityModifier);

            // A public, protected and private signature is assignable to a private signature.
            if (targetAccessibility === ModifierFlags.Private) {
                return true;
            }

            // A public and protected signature is assignable to a protected signature.
            if (targetAccessibility === ModifierFlags.Protected && sourceAccessibility !== ModifierFlags.Private) {
                return true;
            }

            // Only a public signature is assignable to public signature.
            if (targetAccessibility !== ModifierFlags.Protected && !sourceAccessibility) {
                return true;
            }

            if (reportErrors) {
                reportError(Diagnostics.Cannot_assign_a_0_constructor_type_to_a_1_constructor_type, visibilityToString(sourceAccessibility), visibilityToString(targetAccessibility));
            }

            return false;
        }
    }
}