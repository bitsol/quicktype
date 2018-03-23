"use strict";

import { Set, OrderedMap, OrderedSet, Map } from "immutable";

import {
    ClassType,
    Type,
    assertIsClass,
    ClassProperty,
    UnionType,
    ObjectType,
    combineTypeAttributesOfTypes
} from "./Type";
import {
    TypeRef,
    UnionBuilder,
    TypeBuilder,
    TypeLookerUp,
    GraphRewriteBuilder,
    TypeRefUnionAccumulator
} from "./TypeBuilder";
import { panic, assert, defined } from "./Support";
import { TypeNames, namesTypeAttributeKind } from "./TypeNames";
import { TypeAttributes, combineTypeAttributes } from "./TypeAttributes";

function getCliqueProperties(
    clique: ObjectType[],
    makePropertyType: (attributes: TypeAttributes, types: OrderedSet<Type>) => TypeRef
): [OrderedMap<string, ClassProperty>, TypeRef | undefined] {
    let propertyNames = OrderedSet<string>();
    for (const o of clique) {
        propertyNames = propertyNames.union(o.properties.keySeq());
    }

    let properties = propertyNames
        .toArray()
        .map(name => [name, OrderedSet(), false] as [string, OrderedSet<Type>, boolean]);
    let additionalProperties = OrderedSet<Type>();
    for (const o of clique) {
        const additional = o.additionalProperties;
        if (additional !== undefined) {
            additionalProperties = additionalProperties.add(additional);
        }

        for (let i = 0; i < properties.length; i++) {
            let [name, types, isOptional] = properties[i];
            const maybeProperty = o.properties.get(name);
            if (maybeProperty === undefined) {
                isOptional = true;
                if (additional !== undefined) {
                    types = types.add(additional);
                }
            } else {
                if (maybeProperty.isOptional) {
                    isOptional = true;
                }
                types = types.add(maybeProperty.type);
            }

            properties[i][1] = types;
            properties[i][2] = isOptional;
        }
    }

    const additionalPropertiesAttributes = combineTypeAttributesOfTypes(additionalProperties);
    const unifiedAdditionalProperties = makePropertyType(additionalPropertiesAttributes, additionalProperties);

    const unifiedPropertiesArray = properties.map(([name, types, isOptional]) => {
        let attributes = combineTypeAttributesOfTypes(types);
        attributes = namesTypeAttributeKind.setDefaultInAttributes(
            attributes,
            () => new TypeNames(OrderedSet([name]), OrderedSet(), true)
        );
        return [name, new ClassProperty(makePropertyType(attributes, types), isOptional)] as [string, ClassProperty];
    });
    const unifiedProperties = OrderedMap(unifiedPropertiesArray);

    return [unifiedProperties, unifiedAdditionalProperties];
}

export class UnifyUnionBuilder extends UnionBuilder<TypeBuilder & TypeLookerUp, TypeRef[], TypeRef[]> {
    constructor(
        typeBuilder: TypeBuilder & TypeLookerUp,
        private readonly _makeEnums: boolean,
        private readonly _makeObjectTypes: boolean,
        private readonly _makeClassesFixed: boolean,
        private readonly _unifyTypes: (typesToUnify: TypeRef[], typeAttributes: TypeAttributes) => TypeRef
    ) {
        super(typeBuilder);
    }

    protected makeEnum(
        enumCases: string[],
        counts: { [name: string]: number },
        typeAttributes: TypeAttributes,
        forwardingRef: TypeRef | undefined
    ): TypeRef {
        if (this._makeEnums) {
            return this.typeBuilder.getEnumType(typeAttributes, OrderedSet(enumCases), forwardingRef);
        } else {
            return this.typeBuilder.getStringType(typeAttributes, OrderedMap(counts), forwardingRef);
        }
    }

    protected makeObject(
        objectRefs: TypeRef[],
        typeAttributes: TypeAttributes,
        forwardingRef: TypeRef | undefined
    ): TypeRef {
        if (maps.length > 0) {
            const propertyTypes = maps.slice();
            for (let classRef of classes) {
                const c = assertIsClass(classRef.deref()[0]);
                c.properties.forEach(cp => {
                    propertyTypes.push(cp.typeRef);
                });
            }
            const t = this.typeBuilder.getMapType(this._unifyTypes(propertyTypes, Map()), forwardingRef);
            this.typeBuilder.addAttributes(t, typeAttributes);
            return t;
        }
        if (classes.length === 1) {
            const t = this.typeBuilder.reconstituteTypeRef(classes[0], forwardingRef);
            this.typeBuilder.addAttributes(t, typeAttributes);
            return t;
        }
        const maybeTypeRef = this.typeBuilder.lookupTypeRefs(classes, forwardingRef);
        // FIXME: Comparing this to `forwardingRef` feels like it will come
        // crashing on our heads eventually.  The reason we need it here is
        // because `unifyTypes` registers the union that we're supposed to
        // build here as a forwarding ref, and we end up with a circular
        // ref if we just return it here.
        if (maybeTypeRef !== undefined && maybeTypeRef !== forwardingRef) {
            this.typeBuilder.addAttributes(maybeTypeRef, typeAttributes);
            return maybeTypeRef;
        }

        const actualClasses: ClassType[] = classes.map(c => assertIsClass(c.deref()[0]));
        const properties = getCliqueProperties(actualClasses, (names, types) => {
            assert(types.size > 0, "Property has no type");
            return this._unifyTypes(types.map(t => t.typeRef).toArray(), names);
        });

        return this.typeBuilder.getUniqueClassType(typeAttributes, this._makeClassesFixed, properties, forwardingRef);
    }

    protected makeArray(
        arrays: TypeRef[],
        typeAttributes: TypeAttributes,
        forwardingRef: TypeRef | undefined
    ): TypeRef {
        const ref = this.typeBuilder.getArrayType(this._unifyTypes(arrays, Map()), forwardingRef);
        this.typeBuilder.addAttributes(ref, typeAttributes);
        return ref;
    }
}

export function unionBuilderForUnification<T extends Type>(
    typeBuilder: GraphRewriteBuilder<T>,
    makeEnums: boolean,
    makeClassesFixed: boolean,
    conflateNumbers: boolean
): UnionBuilder<TypeBuilder & TypeLookerUp, TypeRef[], TypeRef[]> {
    return new UnifyUnionBuilder(typeBuilder, makeEnums, makeClassesFixed, (trefs, names) =>
        unifyTypes(
            Set(trefs.map(tref => tref.deref()[0])),
            names,
            typeBuilder,
            unionBuilderForUnification(typeBuilder, makeEnums, makeClassesFixed, conflateNumbers),
            conflateNumbers
        )
    );
}

// FIXME: The UnionBuilder might end up not being used.
export function unifyTypes<T extends Type>(
    types: Set<Type>,
    typeAttributes: TypeAttributes,
    typeBuilder: GraphRewriteBuilder<T>,
    unionBuilder: UnionBuilder<TypeBuilder & TypeLookerUp, TypeRef[], TypeRef[]>,
    conflateNumbers: boolean,
    maybeForwardingRef?: TypeRef
): TypeRef {
    if (types.isEmpty()) {
        return panic("Cannot unify empty set of types");
    } else if (types.count() === 1) {
        const first = defined(types.first());
        if (!(first instanceof UnionType)) {
            const tref = typeBuilder.reconstituteTypeRef(first.typeRef, maybeForwardingRef);
            typeBuilder.addAttributes(tref, typeAttributes);
            return tref;
        }
    }

    const typeRefs = types.toArray().map(t => t.typeRef);
    const maybeTypeRef = typeBuilder.lookupTypeRefs(typeRefs, maybeForwardingRef);
    if (maybeTypeRef !== undefined) {
        typeBuilder.addAttributes(maybeTypeRef, typeAttributes);
        return maybeTypeRef;
    }

    const accumulator = new TypeRefUnionAccumulator(conflateNumbers);
    const nestedAttributes = accumulator.addTypes(types);
    typeAttributes = combineTypeAttributes(typeAttributes, nestedAttributes);

    return typeBuilder.withForwardingRef(maybeForwardingRef, forwardingRef => {
        typeBuilder.registerUnion(typeRefs, forwardingRef);
        return unionBuilder.buildUnion(accumulator, false, typeAttributes, forwardingRef);
    });
}
