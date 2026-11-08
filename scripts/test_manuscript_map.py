"""Regression checks for source-derived manuscript equation references."""

from pathlib import Path
import tempfile
import unittest

from manuscript_map import (Node, check_equations_aux, numbered_equations,
                            validate_equation_references)


def document(body):
    return (r'\numberwithin{equation}{section}\begin{document}' + body +
            r'\end{document}')


class EquationNumberingTests(unittest.TestCase):
    def test_unlabeled_equations_and_section_reset(self):
        source = document(r'''
            \section{First}
            \begin{equation} a=b \end{equation}
            \begin{align}\label{eq:a} c=d \end{align}
            \section*{Unnumbered heading}
            \begin{equation}\label{eq:b} e=f \end{equation}
            \section{Second}
            \begin{align}\label{eq:c} g=h \end{align}
        ''')
        self.assertEqual(numbered_equations(source),
                         {'eq:a': '1.2', 'eq:b': '1.3', 'eq:c': '2.1'})

    def test_align_rows_suppression_and_nested_linebreaks(self):
        source = document(r'''
            \section{First}
            \begin{align}
                a &= b \label{eq:a} \\
                c &= d \notag \\
                e &= f \nonumber \\
                g &= h \\
                \begin{aligned} i &= j \\ k &= l \end{aligned}
                    &= \substack{m \\ n} \label{eq:b} \\[1em]
            \end{align}
            \begin{equation}
                \begin{split} x &= y \\ &= z \end{split}\label{eq:c}
            \end{equation}
        ''')
        self.assertEqual(numbered_equations(source),
                         {'eq:a': '1.1', 'eq:b': '1.3', 'eq:c': '1.5'})

    def test_empty_align_rows_receive_numbers(self):
        # These values were checked against an actual amsmath compilation.
        source = document(r'''
            \section{First}
            \begin{align}a=b\\\end{align}
            \begin{equation}\label{eq:next}c=d\end{equation}
            \begin{align}\\a=b\label{eq:afterempty}\end{align}
            \begin{equation}\label{eq:final}c=d\end{equation}
        ''')
        self.assertEqual(numbered_equations(source),
                         {'eq:next': '1.3', 'eq:afterempty': '1.5', 'eq:final': '1.6'})

    def test_starred_displays_and_comments_do_not_advance_counter(self):
        source = document(r'''
            \section{First}
            % \begin{equation}\label{eq:comment} a=b \end{equation}
            \begin{align*} a &= b \\ &= c \end{align*}
            \begin{equation*} 100\% = 1 \end{equation*}
            \begin{align}\label{eq:a} d=e \end{align}
        ''')
        self.assertEqual(numbered_equations(source), {'eq:a': '1.1'})

    def test_comment_after_row_break_preserves_the_break(self):
        source = document(r'''
            \section{First}
            \begin{align}
                100\% &= 1\\% \label{eq:comment} \\
                a &= b\label{eq:a}
            \end{align}
        ''')
        self.assertEqual(numbered_equations(source), {'eq:a': '1.2'})

    def test_removing_numbered_background_shifts_later_labels(self):
        before = document(r'''
            \section{Bosons}
            \begin{align} H=F \end{align}
            \begin{equation}\label{eq:rotation} U=f \end{equation}
        ''')
        after = before.replace(r'\begin{align}', r'\begin{align*}').replace(
            r'\end{align}', r'\end{align*}')
        self.assertEqual(numbered_equations(before), {'eq:rotation': '1.2'})
        self.assertEqual(numbered_equations(after), {'eq:rotation': '1.1'})

    def test_reject_ambiguous_counter_changes(self):
        unsupported = [r'\setcounter{equation}{3}', r'\addtocounter{section}{1}',
                       r'\tag{A}', r'\appendix', r'\counterwithin{equation}{subsection}',
                       r'\renewcommand{\theequation}{X}', r'\begin{subequations}\end{subequations}',
                       r'\begin{gather}a=b\end{gather}']
        for command in unsupported:
            with self.subTest(command=command), self.assertRaisesRegex(ValueError, 'unsupported'):
                numbered_equations(document(command))

    def test_reject_labels_on_unnumbered_rows(self):
        for display in [r'\begin{align*}a=b\label{eq:a}\end{align*}',
                        r'\begin{align}a=b\notag\label{eq:a}\end{align}']:
            with self.subTest(display=display), self.assertRaisesRegex(ValueError, 'unnumbered'):
                numbered_equations(document(display))

    def test_reject_duplicate_labels_and_unclosed_displays(self):
        with self.assertRaisesRegex(ValueError, 'duplicate equation label'):
            numbered_equations(document(
                r'\begin{align}a=b\label{eq:a}\\c=d\label{eq:a}\end{align}'))
        with self.assertRaisesRegex(ValueError, 'unclosed'):
            numbered_equations(document(r'\begin{align}a=b'))

    def test_require_supported_counter_configuration(self):
        with self.assertRaisesRegex(ValueError, 'numberwithin'):
            numbered_equations(r'\begin{document}\end{document}')
        with self.assertRaisesRegex(ValueError, 'numberwithin'):
            numbered_equations(document('').replace('{section}', '{subsection}'))

    def test_aux_crosscheck_ignores_cleveref_metadata(self):
        source = document(r'\section{First}\begin{align}a=b\label{eq:a}\end{align}')
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'manuscript.aux'
            path.write_text(r'''\newlabel{eq:a}{{1.1}{1}{First}{equation.1.1}{}}
                \newlabel{eq:a@cref}{{[equation][1][1]1.1}{[1][1][]1}}''')
            check_equations_aux(source, path)
            path.write_text(r'\newlabel{eq:a}{{1.2}{1}{First}{equation.1.2}{}}')
            with self.assertRaisesRegex(ValueError, 'expected 1.1'):
                check_equations_aux(source, path)
            path.write_text(r'''\newlabel{eq:a}{{1.1}{1}{First}{equation.1.1}{}}
                \newlabel{eq:deleted}{{1.2}{1}{First}{equation.1.2}{}}''')
            with self.assertRaisesRegex(ValueError, 'absent from the manuscript'):
                check_equations_aux(source, path)


class EquationReferenceTests(unittest.TestCase):
    @staticmethod
    def row(title='Rotation (Eq. 6.1)'):
        return {'id': 'rotation', 'label': 'eq:rotation', 'title': title}

    @staticmethod
    def node(display):
        return Node('rotation-node', 'Rotation', [('rotation', display)], [], 1, False)

    def test_computed_number_is_attached_to_record(self):
        row = self.row()
        validate_equation_references([row], {'eq:rotation': '6.1'},
                                     [self.node('the rotation formula')])
        self.assertEqual(row['equation'], '6.1')

    def test_reject_stale_or_missing_equation_title(self):
        for title in ['Rotation (Eq. 6.3)', 'Rotation']:
            with self.subTest(title=title), self.assertRaisesRegex(ValueError, 'Eq. 6.1'):
                validate_equation_references([self.row(title)], {'eq:rotation': '6.1'}, [])

    def test_every_equation_label_must_be_indexed(self):
        with self.assertRaisesRegex(ValueError, 'missing from manuscript index'):
            validate_equation_references([self.row()],
                                         {'eq:rotation': '6.1', 'eq:new': '6.2'}, [])

    def test_numeric_blueprint_captions_must_match_anchor(self):
        for display in ['Eq.~(6.1)', 'Equation (6.1)', 'rotation, Eq. 6.1']:
            validate_equation_references([self.row()], {'eq:rotation': '6.1'},
                                         [self.node(display)])
        with self.assertRaisesRegex(ValueError, 'does not match'):
            validate_equation_references([self.row()], {'eq:rotation': '6.1'},
                                         [self.node('Eq.~(6.3)')])

    def test_equation_references_outside_nodes_are_also_checked(self):
        for macro in ['paperref', 'noderef', 'proofref']:
            source = '\\' + macro + r'{rotation}{Eq.~(6.3)}'
            with self.subTest(macro=macro), self.assertRaisesRegex(ValueError, 'does not match'):
                validate_equation_references([self.row()], {'eq:rotation': '6.1'}, [], source)

    def test_equation_title_needs_equation_source_label(self):
        with self.assertRaisesRegex(ValueError, 'requires a numbered equation label'):
            validate_equation_references([self.row()], {}, [])


if __name__ == '__main__':
    unittest.main()
