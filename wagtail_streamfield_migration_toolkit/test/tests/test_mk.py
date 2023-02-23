from django.test import SimpleTestCase
from wagtail import blocks

from wagtail_streamfield_migration_toolkit.mk import (
    Cons,
    Nil,
    string,
    appendo,
    assoco,
    cdro,
    conda,
    conj,
    conso,
    disj,
    eq,
    fail,
    fresh,
    from_python,
    goal,
    ifte,
    joino,
    neq,
    notnullo,
    nullo,
    rembero,
    run,
    run_all,
    succeed,
    to_python,
    walk_all,
)
from wagtail_streamfield_migration_toolkit.compare import deep_deconstruct


def stream_block_diffo(old_block, new_block, path, out):
    return compound_block_diffo(old_block, new_block, path, out)


def atomic_block_diffo(old_spec, new_spec, path, diff):
    return spec_diffo(old_spec, new_spec, path, diff)


def list_block_diffo():
    return fail()


def struct_block_diffo(old_block, new_block, path, out):
    return compound_block_diffo(old_block, new_block, path, out)


def spec_diffo(old_spec, new_spec, path, diff):
    return disj(
        nullo(old_spec) & nullo(new_spec) & nullo(diff),
        fresh(
            lambda k, d, e, rest_old_spec, rest_new_spec: conj(
                notnullo(old_spec),
                notnullo(new_spec),
                conso((k, d), rest_old_spec, old_spec),
                conso((k, e), rest_new_spec, new_spec),
                neq(k, string("local_blocks")),
                neq(k, string("child_block")),
                disj(
                    eq(d, e) & spec_diffo(rest_old_spec, rest_new_spec, path, diff),
                    fresh(
                        lambda res: conj(
                            neq(d, e),
                            conso((path, string("change_opt"), k, d, e), res, diff),
                            spec_diffo(rest_old_spec, rest_new_spec, path, res),
                        )
                    ),
                ),
            ),
        ),
    )


def compound_block_diffo(old_block, new_block, path, out):
    return fresh(
        lambda _, __, old_spec, new_spec: conj(
            eq((_, old_spec), old_block),
            eq((__, new_spec), new_block),
            fresh(
                lambda _, __, old_children, new_children: conj(
                    assoco(string("local_blocks"), old_spec, (_, old_children)),
                    assoco(string("local_blocks"), new_spec, (__, new_children)),
                    map_child_blocks(old_children, new_children, path, out),
                )
            ),
        )
    )


# def map_child_blocks(old_blocks, new_blocks, path, diff):
#     return disj(
#         nullo(old_blocks) & nullo(diff),
#         fresh(
#             lambda name, spec, rest_blocks, res, this_path, rest_new_blocks: conda(
#                 # TODO: add case for added child
#                 conj(
#                     # new blocks is null, must have been removed
#                     nullo(new_blocks),
#                     conso((name, spec), rest_blocks, old_blocks),
#                     joino(path, name, string("."), this_path),
#                     conso((this_path, string("remove")), res, diff),
#                     map_child_blocks(rest_blocks, new_blocks, path, res),
#                 ),
#                 conj(
#                     # Try to map the old child block to a new child - this might fail
#                     notnullo(new_blocks),
#                     conso((name, spec), rest_blocks, old_blocks),
#                     joino(path, name, string("."), this_path),
#                     map_child_block(
#                         name, spec, new_blocks, this_path, rest_new_blocks, diff
#                     ),
#                     map_child_blocks(rest_blocks, rest_new_blocks, path, diff),
#                 ),
#                 conj(
#                     # Recursive case - couldn't map the block
#                     notnullo(new_blocks),
#                     conso((name, spec), rest_blocks, old_blocks),
#                     joino(path, name, string("."), this_path),
#                     conso((this_path, string("unmapped")), res, diff),
#                     map_child_blocks(rest_blocks, new_blocks, path, res),
#                 ),
#             )
#         ),
#     )


def map_child_blocks(old_blocks, new_blocks, path, diff):
    return disj(
        nullo(old_blocks) & nullo(diff),
        fresh(
            lambda name, spec, rest_blocks, rest_new_blocks, this_path, next_diff, child_diff: conj(
                joino(path, name, string("."), this_path),
                conda(
                    conj(
                        # new_blocks is null, old block must have been removed
                        nullo(new_blocks),
                        conso((name, spec), rest_blocks, old_blocks),
                        conso((this_path, string("remove")), next_diff, diff),
                        map_child_blocks(rest_blocks, new_blocks, path, next_diff),
                    ),
                    conj(
                        # Try to map the old child block to a new child - this might fail
                        notnullo(new_blocks),
                        conso((name, spec), rest_blocks, old_blocks),
                        map_child_block(
                            name,
                            spec,
                            new_blocks,
                            this_path,
                            rest_new_blocks,
                            child_diff,
                        ),
                        conso(next_diff, child_diff, diff),
                        map_child_blocks(rest_blocks, rest_new_blocks, path, next_diff),
                    ),
                    conj(
                        # Must have added blocks
                        nullo(old_blocks),
                        notnullo(new_blocks),
                        conso((name, spec), rest_new_blocks, new_blocks),
                        conso((path, "add", name), next_diff, diff),
                        map_child_blocks(old_blocks, rest_new_blocks, path, next_diff),
                    ),
                    conj(
                        # Recursive case - couldn't map the block
                        notnullo(new_blocks),
                        conso((name, spec), rest_blocks, old_blocks),
                        conso((this_path, string("unmapped")), next_diff, diff),
                        map_child_blocks(rest_blocks, new_blocks, path, next_diff),
                    ),
                ),
            ),
        ),
    )


def map_child_block(name, spec, new_blocks, path, rest_new_blocks, diff):
    @goal
    def map_child_block_goal(state):
        return disj(
            nullo(new_blocks) & nullo(diff),
            fresh(
                lambda a, d, new_spec: disj(
                    conj(
                        # There is a block with the same name, maybe the spec changed
                        rembero((name, new_spec), new_blocks, rest_new_blocks),
                        neq(new_blocks, rest_new_blocks),
                        same_blocko(spec, new_spec, path, diff),
                    ),
                    conj(
                        # No block with the same name
                        rembero((name, new_spec), new_blocks, new_blocks),
                        map_child_block_by_value(name, spec, new_blocks, path, diff),
                    ),
                )
            ),
        )(state)

    return map_child_block_goal


def map_child_block_by_value(old_name, spec, new_blocks, path, diff):
    # Don't do a disj with a nullo(new_blocks)&nullo(diff) clause, as
    # in that case we've reached the end of the list of new_blocks so
    # don't need to contribute further values
    return fresh(
        lambda new_name, new_spec, rest_new_blocks, res, _: conj(
            # We want to compare by block spec only, not name
            neq(old_name, new_name),
            conso((new_name, new_spec), rest_new_blocks, new_blocks),
            same_blocko(spec, new_spec, path, res),
            disj(
                conso((path, "rename", new_name), res, diff),
                conj(
                    map_child_block_by_value(
                        old_name, spec, rest_new_blocks, path, diff
                    ),
                ),
            ),
        )
    )


def same_blocko(old_block_spec, new_block_spec, path, diff):
    return fresh(
        lambda old_type, new_type, old_spec, new_spec: conj(
            eq((old_type, old_spec), old_block_spec),
            eq((new_type, new_spec), new_block_spec),
            eq(old_type, new_type),
            disj(
                atomic_block_diffo(old_spec, new_spec, path, diff),
                stream_block_diffo(old_block_spec, new_block_spec, path, diff),
            ),
        )
    )


class TestMkCompare(SimpleTestCase):
    def test_second_block_from_diff(self):
        block_1 = blocks.CharBlock(required=True)
        _, args = deep_deconstruct(block_1)
        changes = from_python([(string(""), "change_opt", "required", True, False)])
        result = run_all(
            lambda q: spec_diffo(from_python(args), q, string(""), changes)
        )
        self.assertEqual(len(result), 1)
        self.assertEqual(
            result[0],
            [
                ("required", False),
                ("help_text", None),
                ("max_length", None),
                ("min_length", None),
                ("validators", ()),
            ],
        )

    def test_first_block_from_diff(self):
        block_1 = blocks.CharBlock(required=True)
        _, args = deep_deconstruct(block_1)
        changes = from_python(
            [
                ("", "change_opt", "required", False, True),
                ("", "change_opt", "help_text", "foobar", None),
            ]
        )
        result = run_all(
            lambda q: spec_diffo(q, from_python(args), string(""), changes)
        )
        self.assertEqual(len(result), 1)
        self.assertEqual(
            result[0],
            [
                ("required", False),
                ("help_text", "foobar"),
                ("max_length", None),
                ("min_length", None),
                ("validators", ()),
            ],
        )

    def test_stream_child_removed(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock([])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0], [("text", "remove")])

    def test_stream_child_added(self):
        block_1 = blocks.StreamBlock([])
        block_2 = blocks.StreamBlock([("text", blocks.CharBlock())])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        breakpoint()
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0], [("text", "remove")])

    def test_stream_child_removed_when_multiple_child_blocks(self):
        block_1 = blocks.StreamBlock(
            [("text", blocks.CharBlock()), ("number", blocks.IntegerBlock())]
        )
        block_2 = blocks.StreamBlock([("number", blocks.IntegerBlock())])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0], [("text", "remove")])

    def test_stream_child_spec_changed(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock([("text", blocks.CharBlock(max_length=11))])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0], [("text", "change_opt", "max_length", None, 11)])

    def test_stream_child_name_changed(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock([("not_text", blocks.CharBlock())])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0], [("text", "rename", "not_text")])

    def test_stream_child_name_and_spec_changed(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock(
            [
                ("not_text", blocks.CharBlock(required=False, max_length=1)),
                ("really_not_text", blocks.CharBlock(min_length=12)),
            ]
        )
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        self.assertEqual(len(result), 2)
        self.assertEqual(
            result,
            [
                [
                    ("text", "rename", "not_text"),
                    ("text", "change_opt", "required", True, False),
                    ("text", "change_opt", "max_length", None, 1),
                ],
                [
                    ("text", "rename", "really_not_text"),
                    ("text", "change_opt", "min_length", None, 12),
                ],
            ],
        )

    def test_nested_stream_child_name_changed(self):
        inner_stream_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        inner_stream_2 = blocks.StreamBlock([("not_text", blocks.CharBlock())])
        block_1 = blocks.StreamBlock([("inner_stream", inner_stream_1)])
        block_2 = blocks.StreamBlock([("inner_stream", inner_stream_2)])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0], [("inner_stream.text", "rename", "not_text")])

    def test_different_block_types_fails(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock([("not_text", blocks.IntegerBlock())])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0], [("text", "unmapped")])

    def test_struct_block(self):
        struct_1 = blocks.StructBlock([("number", blocks.IntegerBlock())])
        struct_2 = blocks.StructBlock(
            [("more_number", blocks.IntegerBlock(min_value=11))]
        )
        block_1 = blocks.StreamBlock([("struct", struct_1)])
        block_2 = blocks.StreamBlock([("struct", struct_2)])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string(""), q))
        # breakpoint()
        self.assertEqual(len(result), 1)
        self.assertEqual(
            result[0],
            [
                ("struct.number", "rename", "more_number"),
                ("struct.number", "change_opt", "min_value", None, 11),
            ],
        )
