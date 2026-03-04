from flask import Flask, render_template, request, redirect, session, flash, url_for, Response
from flask import jsonify
from werkzeug.security import generate_password_hash, check_password_hash
import mysql.connector, os
import re
from functools import wraps
import datetime 
import random
import traceback
import urllib.parse
import csv
from io import StringIO
from io import BytesIO
from zipfile import ZipFile, ZIP_DEFLATED
from html import unescape
from dotenv import load_dotenv


app = Flask(__name__)
app.secret_key = "securekey123"

# ---------------- DB CONNECTION ----------------
DEPARTMENTS = ["Computer", "Mechanical", "Electrical", "Civil"]

load_dotenv(override=True)


def _get_env_value(primary_key, *fallback_keys):
    for key in (primary_key, *fallback_keys):
        value = os.getenv(key)
        if value is not None and str(value).strip():
            return str(value).strip()
    return None


class DBConnection:
    def __init__(self):
        db_host = _get_env_value("DB_HOST", "HOST")
        db_user = _get_env_value("DB_USER", "USE")
        db_password = _get_env_value("DB_PASSWORD", "PASSWORD")
        db_database = _get_env_value("DB_DATABASE", "DATABASE")
        db_port_raw = _get_env_value("DB_PORT", "PORT") or "3306"

        missing = []
        if not db_host:
            missing.append("DB_HOST")
        if not db_user:
            missing.append("DB_USER")
        if db_password is None:
            missing.append("DB_PASSWORD")
        if not db_database:
            missing.append("DB_DATABASE")
        if missing:
            raise RuntimeError(
                f"Missing required database environment variables: {', '.join(missing)}"
            )

        try:
            db_port = int(db_port_raw)
        except ValueError as exc:
            raise RuntimeError("DB_PORT must be a valid integer.") from exc

        self.conn = mysql.connector.connect(
            host=db_host,
            user=db_user,
            password=db_password,
            database=db_database,
            port=db_port,
        )

    class _StaticCursor:
        def __init__(self, rows):
            self._rows = rows
            self.rowcount = len(rows)

        def fetchone(self):
            return self._rows[0] if self._rows else None

        def fetchall(self):
            return list(self._rows)

        def __iter__(self):
            return iter(self._rows)

        def close(self):
            return None

    def _table_exists(self, table_name):
        cursor = self.conn.cursor(dictionary=True)
        cursor.execute(
            """
            SELECT TABLE_NAME
            FROM INFORMATION_SCHEMA.TABLES
            WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = %s
            LIMIT 1
            """,
            (table_name,),
        )
        row = cursor.fetchone()
        cursor.close()
        return bool(row)

    def _index_exists(self, table_name, index_name):
        cursor = self.conn.cursor(dictionary=True)
        cursor.execute(
            """
            SELECT INDEX_NAME
            FROM INFORMATION_SCHEMA.STATISTICS
            WHERE TABLE_SCHEMA = DATABASE()
                AND TABLE_NAME = %s
                AND INDEX_NAME = %s
            LIMIT 1
            """,
            (table_name, index_name),
        )
        row = cursor.fetchone()
        cursor.close()
        return bool(row)

    def _handle_sqlite_meta_query(self, query):
        normalized = " ".join(query.strip().split())

        table_exists_match = re.search(
            r"select\s+(?:1|name)\s+from\s+sqlite_master\s+where\s+type='table'\s+and\s+name='([^']+)'",
            normalized,
            flags=re.IGNORECASE,
        )
        if table_exists_match:
            table_name = table_exists_match.group(1)
            if self._table_exists(table_name):
                return self._StaticCursor([{"name": table_name}])
            return self._StaticCursor([])

        pragma_table_info_match = re.search(
            r"pragma\s+table_info\(([^)]+)\)",
            normalized,
            flags=re.IGNORECASE,
        )
        if pragma_table_info_match:
            table_name = pragma_table_info_match.group(1).strip().strip("'\"`")
            cursor = self.conn.cursor(dictionary=True)
            cursor.execute(
                """
                SELECT COLUMN_NAME, COLUMN_TYPE, IS_NULLABLE, COLUMN_DEFAULT, COLUMN_KEY
                FROM INFORMATION_SCHEMA.COLUMNS
                WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = %s
                ORDER BY ORDINAL_POSITION
                """,
                (table_name,),
            )
            meta_rows = cursor.fetchall()
            cursor.close()
            rows = []
            for idx, row in enumerate(meta_rows):
                rows.append(
                    (
                        idx,
                        row["COLUMN_NAME"],
                        row["COLUMN_TYPE"],
                        0 if row["IS_NULLABLE"] == "YES" else 1,
                        row["COLUMN_DEFAULT"],
                        1 if row["COLUMN_KEY"] == "PRI" else 0,
                    )
                )
            return self._StaticCursor(rows)

        pragma_fk_match = re.search(
            r"pragma\s+foreign_key_list\(([^)]+)\)",
            normalized,
            flags=re.IGNORECASE,
        )
        if pragma_fk_match:
            table_name = pragma_fk_match.group(1).strip().strip("'\"`")
            cursor = self.conn.cursor(dictionary=True)
            cursor.execute(
                """
                SELECT CONSTRAINT_NAME, REFERENCED_TABLE_NAME, COLUMN_NAME, REFERENCED_COLUMN_NAME
                FROM INFORMATION_SCHEMA.KEY_COLUMN_USAGE
                WHERE TABLE_SCHEMA = DATABASE()
                    AND TABLE_NAME = %s
                    AND REFERENCED_TABLE_NAME IS NOT NULL
                ORDER BY CONSTRAINT_NAME, ORDINAL_POSITION
                """,
                (table_name,),
            )
            fk_rows = cursor.fetchall()
            cursor.close()
            out = []
            constraint_ids = {}
            next_id = 0
            seq_by_constraint = {}
            for row in fk_rows:
                cname = row["CONSTRAINT_NAME"]
                if cname not in constraint_ids:
                    constraint_ids[cname] = next_id
                    seq_by_constraint[cname] = 0
                    next_id += 1
                out.append(
                    (
                        constraint_ids[cname],
                        seq_by_constraint[cname],
                        row["REFERENCED_TABLE_NAME"],
                        row["COLUMN_NAME"],
                        row["REFERENCED_COLUMN_NAME"],
                        None,
                        None,
                        None,
                    )
                )
                seq_by_constraint[cname] += 1
            return self._StaticCursor(out)

        if re.match(r"^\s*pragma\s+foreign_keys\s*=\s*(off|on)\s*;?\s*$", query, flags=re.IGNORECASE):
            return self._StaticCursor([])

        index_if_not_exists_match = re.search(
            r"create\s+unique\s+index\s+if\s+not\s+exists\s+([a-zA-Z0-9_]+)\s+on\s+([a-zA-Z0-9_]+)\s*\(",
            normalized,
            flags=re.IGNORECASE,
        )
        if index_if_not_exists_match:
            index_name = index_if_not_exists_match.group(1)
            table_name = index_if_not_exists_match.group(2)
            if self._index_exists(table_name, index_name):
                return self._StaticCursor([])

        return None

    def _normalize_sql(self, query):
        query = re.sub(r"--.*?$", "", query, flags=re.MULTILINE)
        query = re.sub(r"\bINSERT\s+OR\s+IGNORE\s+INTO\b", "INSERT IGNORE INTO", query, flags=re.IGNORECASE)
        query = re.sub(r"\bINSERT\s+OR\s+REPLACE\s+INTO\b", "REPLACE INTO", query, flags=re.IGNORECASE)
        query = re.sub(
            r"\bCREATE\s+UNIQUE\s+INDEX\s+IF\s+NOT\s+EXISTS\b",
            "CREATE UNIQUE INDEX",
            query,
            flags=re.IGNORECASE,
        )
        query = re.sub(
            r"(\bCREATE\s+(?:UNIQUE\s+)?INDEX\b[\s\S]*?\))\s*WHERE\s+[\s\S]*$",
            r"\1",
            query,
            flags=re.IGNORECASE,
        )
        query = re.sub(
            r"\bON\s+CONFLICT\s*\([^)]+\)\s*DO\s+UPDATE\s+SET\b",
            "ON DUPLICATE KEY UPDATE",
            query,
            flags=re.IGNORECASE,
        )
        query = re.sub(r"\bexcluded\.([a-zA-Z_][a-zA-Z0-9_]*)", r"VALUES(\1)", query, flags=re.IGNORECASE)
        query = re.sub(
            r"\bINTEGER\s+PRIMARY\s+KEY\s+AUTOINCREMENT\b",
            "INT AUTO_INCREMENT PRIMARY KEY",
            query,
            flags=re.IGNORECASE,
        )
        query = re.sub(r"\bAUTOINCREMENT\b", "AUTO_INCREMENT", query, flags=re.IGNORECASE)
        query = re.sub(r"\bTEXT\b", "VARCHAR(255)", query, flags=re.IGNORECASE)
        if re.search(r"^\s*CREATE\s+TABLE", query, flags=re.IGNORECASE):
            query = re.sub(
                r",\s*FOREIGN\s+KEY\s*\([^)]+\)\s*REFERENCES\s+[^\s,(]+(?:\s*\([^)]+\))?",
                "",
                query,
                flags=re.IGNORECASE,
            )
            query = re.sub(
                r"\s*FOREIGN\s+KEY\s*\([^)]+\)\s*REFERENCES\s+[^\s,(]+(?:\s*\([^)]+\))?\s*,?",
                "",
                query,
                flags=re.IGNORECASE,
            )
            query = re.sub(r",\s*\)", "\n)", query)
        query = re.sub(r"datetime\(\s*'now'\s*\)", "CURRENT_TIMESTAMP", query, flags=re.IGNORECASE)
        query = re.sub(r"date\(\s*'now'\s*\)", "CURRENT_DATE", query, flags=re.IGNORECASE)
        query = query.replace("?", "%s")
        return query

    def execute(self, query, params=None):
        meta_cursor = self._handle_sqlite_meta_query(query)
        if meta_cursor is not None:
            return meta_cursor

        query = self._normalize_sql(query)
        cursor = self.conn.cursor(dictionary=True)
        cursor.execute(query, params or ())
        return cursor

    def executemany(self, query, seq_params):
        query = self._normalize_sql(query)
        cursor = self.conn.cursor(dictionary=True)
        cursor.executemany(query, seq_params)
        return cursor

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.conn:
            self.conn.close()

    def __getattr__(self, name):
        return getattr(self.conn, name)


def get_db_connection():
    return DBConnection()

def _parse_db_datetime(value):
    if not value:
        return None
    try:
        return datetime.datetime.fromisoformat(str(value))
    except ValueError:
        try:
            return datetime.datetime.strptime(str(value), "%Y-%m-%d %H:%M:%S")
        except ValueError:
            return None

def _csv_response(filename, headers, rows):
    output = StringIO()
    writer = csv.writer(output)
    writer.writerow(headers)
    for row in rows:
        writer.writerow(row)
    return Response(
        output.getvalue(),
        mimetype="text/csv",
        headers={"Content-Disposition": f"attachment; filename={filename}"}
    )

def _xml_escape(value):
    text = "" if value is None else str(value)
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
        .replace("'", "&apos;")
    )

def _excel_col_name(index):
    name = ""
    current = index
    while current > 0:
        current, rem = divmod(current - 1, 26)
        name = chr(65 + rem) + name
    return name

def _build_sheet_xml(rows):
    xml = [
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
        '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><sheetData>'
    ]
    for r_idx, row in enumerate(rows, start=1):
        xml.append(f'<row r="{r_idx}">')
        for c_idx, value in enumerate(row, start=1):
            if value is None or value == "":
                continue
            cell_ref = f"{_excel_col_name(c_idx)}{r_idx}"
            if isinstance(value, (int, float)):
                xml.append(f'<c r="{cell_ref}"><v>{value}</v></c>')
            else:
                text = _xml_escape(unescape(str(value)))
                xml.append(f'<c r="{cell_ref}" t="inlineStr"><is><t xml:space="preserve">{text}</t></is></c>')
        xml.append('</row>')
    xml.append('</sheetData></worksheet>')
    return "".join(xml)

def _xlsx_response(filename, sheets):
    memory = BytesIO()
    with ZipFile(memory, "w", ZIP_DEFLATED) as zf:
        zf.writestr(
            "[Content_Types].xml",
            '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
            '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
            '<Default Extension="xml" ContentType="application/xml"/>'
            '<Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
            + "".join(
                f'<Override PartName="/xl/worksheets/sheet{i}.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'
                for i in range(1, len(sheets) + 1)
            )
            + "</Types>"
        )
        zf.writestr(
            "_rels/.rels",
            '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
            '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/>'
            '</Relationships>'
        )
        workbook_xml = [
            '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
            '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
            'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets>'
        ]
        rels_xml = [
            '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
            '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        ]
        for i, sheet in enumerate(sheets, start=1):
            name = _xml_escape(sheet["name"][:31] or f"Sheet{i}")
            workbook_xml.append(f'<sheet name="{name}" sheetId="{i}" r:id="rId{i}"/>')
            rels_xml.append(
                f'<Relationship Id="rId{i}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet{i}.xml"/>'
            )
            zf.writestr(f"xl/worksheets/sheet{i}.xml", _build_sheet_xml(sheet["rows"]))
        workbook_xml.append("</sheets></workbook>")
        rels_xml.append("</Relationships>")
        zf.writestr("xl/workbook.xml", "".join(workbook_xml))
        zf.writestr("xl/_rels/workbook.xml.rels", "".join(rels_xml))

    memory.seek(0)
    return Response(
        memory.getvalue(),
        mimetype="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
        headers={"Content-Disposition": f"attachment; filename={filename}"}
    )

def _difficulty_bucket(correct_count, attempts):
    if not attempts:
        return "no_data"
    rate = correct_count / attempts
    if rate >= 0.8:
        return "easy"
    if rate >= 0.5:
        return "medium"
    return "difficult"

def _safe_float(value, default=0.0):
    try:
        if value is None:
            return default
        return float(value)
    except (TypeError, ValueError):
        return default

def _build_kahoot_style_sheets(
    quiz_name,
    played_on,
    hosted_by,
    players_count,
    final_rows,
    questions,
    question_accuracy_map,
    raw_rows
):
    question_id_to_number = {q["question_id"]: i + 1 for i, q in enumerate(questions)}
    question_id_to_options = {q["question_id"]: (q.get("options") or [])[:6] for q in questions}
    question_id_to_correct_answers = {q["question_id"]: q.get("correct_answers", "") for q in questions}
    question_id_to_time = {q["question_id"]: q.get("time_limit", 20) for q in questions}

    per_player_question_score = {}
    current_total = {}
    raw_data_rows = []

    for raw in raw_rows:
        qid = raw.get("question_id")
        q_no = question_id_to_number.get(qid, "")
        opts = question_id_to_options.get(qid, [])
        padded_opts = opts + [""] * (6 - len(opts))
        player_name = raw.get("player_name") or ""
        session_id = raw.get("session_id")
        score = _safe_float(raw.get("score_awarded"), 0.0)
        key = (session_id, player_name)
        current_total[key] = _safe_float(current_total.get(key), 0.0) + score
        response_ms = _safe_float(raw.get("response_ms"), 0.0)
        allotted = _safe_float(raw.get("time_limit"), question_id_to_time.get(qid, 20))
        allotted = allotted if allotted > 0 else 20
        answer_time_pct = round((response_ms / (allotted * 1000)) * 100, 2) if allotted else 0
        score_flag = 1 if int(_safe_float(raw.get("is_correct"), 0)) == 1 else 0
        incorrect_flag = 0 if score_flag == 1 else 1

        per_player_question_score[(player_name, qid)] = _safe_float(
            per_player_question_score.get((player_name, qid)), 0.0
        ) + score

        raw_data_rows.append([
            q_no,
            raw.get("question_text") or "",
            padded_opts[0],
            padded_opts[1],
            padded_opts[2],
            padded_opts[3],
            padded_opts[4],
            padded_opts[5],
            question_id_to_correct_answers.get(qid, ""),
            allotted,
            player_name,
            raw.get("answer") or "",
            "Correct" if score_flag else "Incorrect",
            score_flag,
            incorrect_flag,
            score,
            score,
            round(current_total[key], 2),
            answer_time_pct,
            round(response_ms / 1000, 3)
        ])

    overview_rows = [
        [quiz_name],
        ["Played on", played_on],
        ["Hosted by", hosted_by],
        ["Played with", f"{players_count} players"]
    ]

    final_score_rows = [
        [quiz_name],
        ["Final Scores"],
        ["Rank", "Player", "Total Score (points)", "Correct Answers", "Incorrect Answers"]
    ]
    for idx, row in enumerate(final_rows, start=1):
        final_score_rows.append([
            idx,
            row.get("player_name", ""),
            _safe_float(row.get("score"), 0.0),
            int(_safe_float(row.get("correct_answers"), 0)),
            int(_safe_float(row.get("incorrect_answers"), 0))
        ])

    summary_header = ["Rank", "Player", "Total Score (points)"]
    summary_title = [quiz_name]
    summary_subtitle = ["Kahoot! Summary"]
    for q in questions:
        qn = question_id_to_number.get(q["question_id"], "")
        summary_header.extend([f"Q{qn}", q["question_text"]])
        summary_title.extend(["", ""])
        summary_subtitle.extend(["", ""])

    summary_rows = [summary_title, summary_subtitle, summary_header]
    for idx, row in enumerate(final_rows, start=1):
        data = [idx, row.get("player_name", ""), _safe_float(row.get("score"), 0.0)]
        for q in questions:
            qscore = per_player_question_score.get((row.get("player_name", ""), q["question_id"]), 0.0)
            data.extend([round(qscore, 2), ""])
        summary_rows.append(data)

    sheets = [
        {"name": "Overview", "rows": overview_rows},
        {"name": "Final Scores", "rows": final_score_rows},
        {"name": "Kahoot! Summary", "rows": summary_rows}
    ]

    for q in questions:
        qn = question_id_to_number.get(q["question_id"], "")
        accuracy = _safe_float(question_accuracy_map.get(q["question_id"]), 0.0)
        sheets.append({
            "name": f"{qn} Quiz",
            "rows": [
                [quiz_name],
                [f"{qn} Quiz", q["question_text"]],
                ["Correct answers", "", q.get("correct_answers", "")],
                ["Players correct (%)", "", round(accuracy, 6)]
            ]
        })

    sheets.append({
        "name": "RawReportData Data",
        "rows": [
            [
                "Question Number",
                "Question",
                "Answer 1",
                "Answer 2",
                "Answer 3",
                "Answer 4",
                "Answer 5",
                "Answer 6",
                "Correct Answers",
                "Time Allotted to Answer (seconds)",
                "Player",
                "Answer",
                "Correct / Incorrect",
                "Correct",
                "Incorrect",
                "Score (points)",
                "Score without Answer Streak Bonus (points)",
                "Current Total Score (points)",
                "Answer Time (%)",
                "Answer Time (seconds)"
            ]
        ] + raw_data_rows
    })

    return sheets

def _get_live_question_state(conn, session_data):
    if not session_data:
        return {"finished": True, "started": False}

    if session_data["started"] != 1:
        return {"finished": False, "started": False}

    current_q = session_data["current_question"] or 0
    question = conn.execute(
        "SELECT * FROM questions WHERE quiz_id=? LIMIT 1 OFFSET ?",
        (session_data["quiz_id"], current_q)
    ).fetchone()

    if not question:
        return {"finished": True, "started": True}

    options = conn.execute(
        "SELECT option_text, is_correct FROM options WHERE question_id=? ORDER BY option_id",
        (question["question_id"],)
    ).fetchall()

    started_at = _parse_db_datetime(session_data["question_started_at"])
    now_utc = datetime.datetime.utcnow()
    if not started_at:
        started_at = now_utc

    time_limit = question["time_limit"] or 20
    elapsed = max(0, int((now_utc - started_at).total_seconds()))
    time_left = max(0, time_limit - elapsed)

    correct_option = next((opt["option_text"] for opt in options if opt["is_correct"] == 1), None)

    return {
        "finished": False,
        "started": True,
        "question_id": question["question_id"],
        "question_index": current_q,
        "question_number": current_q + 1,
        "question_text": question["question_text"],
        "time_limit": time_limit,
        "time_left": time_left,
        "phase": "question" if time_left > 0 else "reveal",
        "options": [opt["option_text"] for opt in options],
        "correct_option": correct_option,
    }

def _get_answer_breakdown(conn, session_id, question_id):
    rows = conn.execute(
        """
        SELECT answer, player_name
        FROM player_answers
        WHERE session_id=? AND question_id=?
        ORDER BY submitted_at ASC, answer_id ASC
        """,
        (session_id, question_id)
    ).fetchall()

    breakdown = {}
    for row in rows:
        answer = row["answer"]
        if answer not in breakdown:
            breakdown[answer] = {"count": 0, "players": []}
        breakdown[answer]["count"] += 1
        breakdown[answer]["players"].append(row["player_name"])

    return breakdown

def _get_live_leaderboard_rows(conn, session_id):
    scores = conn.execute(
        """
        SELECT
            p.nickname AS player_name,
            COALESCE(a.score, 0) AS score,
            COALESCE(a.correct_answers, 0) AS correct_answers,
            COALESCE(a.time_taken, 0) AS time_taken
        FROM participants p
        LEFT JOIN (
            SELECT
                player_name,
                COALESCE(SUM(score_awarded), 0) AS score,
                COALESCE(SUM(is_correct), 0) AS correct_answers,
                COALESCE(SUM(CASE WHEN is_correct=1 THEN response_ms ELSE 0 END), 0) AS time_taken
            FROM player_answers
            WHERE session_id=?
            GROUP BY player_name
        ) a ON a.player_name = p.nickname
        WHERE p.session_id=?
        ORDER BY score DESC, correct_answers DESC, time_taken ASC, player_name ASC
        """,
        (session_id, session_id)
    ).fetchall()

    return [dict(row) for row in scores]

def _get_player_live_rank_details(conn, session_id, player_name):
    rows = _get_live_leaderboard_rows(conn, session_id)
    total_players = len(rows)
    if total_players == 0:
        return {
            "rank": None,
            "total_players": 0,
            "score": 0,
            "points_to_next": None,
            "next_player": None
        }

    for idx, row in enumerate(rows):
        if row["player_name"] == player_name:
            rank = idx + 1
            score = row["score"] or 0
            if rank == 1:
                return {
                    "rank": rank,
                    "total_players": total_players,
                    "score": score,
                    "points_to_next": 0,
                    "next_player": None
                }
            above = rows[idx - 1]
            points_to_next = max(0, (above["score"] or 0) - score)
            return {
                "rank": rank,
                "total_players": total_players,
                "score": score,
                "points_to_next": points_to_next,
                "next_player": above["player_name"]
            }

    return {
        "rank": None,
        "total_players": total_players,
        "score": 0,
        "points_to_next": None,
        "next_player": None
    }

def _get_question_ranking(conn, session_id, question_id):
    participants = conn.execute(
        "SELECT nickname FROM participants WHERE session_id=? ORDER BY nickname ASC",
        (session_id,)
    ).fetchall()

    answer_rows = conn.execute(
        """
        SELECT player_name, answer, is_correct, response_ms, answer_id
        FROM player_answers
        WHERE session_id=? AND question_id=?
        ORDER BY answer_id ASC
        """,
        (session_id, question_id)
    ).fetchall()

    first_answer_by_player = {}
    for row in answer_rows:
        player = row["player_name"]
        if player not in first_answer_by_player:
            first_answer_by_player[player] = dict(row)

    ranking = []
    for participant in participants:
        name = participant["nickname"]
        row = first_answer_by_player.get(name)
        if not row:
            ranking.append({
                "player_name": name,
                "answer": None,
                "is_correct": 0,
                "response_ms": None,
                "status": "no_answer"
            })
            continue

        status = "correct" if row["is_correct"] == 1 else "wrong"
        ranking.append({
            "player_name": name,
            "answer": row["answer"],
            "is_correct": 1 if row["is_correct"] == 1 else 0,
            "response_ms": row["response_ms"],
            "status": status
        })

    def sort_key(item):
        if item["status"] == "correct":
            return (0, item["response_ms"] if item["response_ms"] is not None else 10**12, item["player_name"].lower())
        if item["status"] == "wrong":
            return (1, item["response_ms"] if item["response_ms"] is not None else 10**12, item["player_name"].lower())
        return (2, 10**12, item["player_name"].lower())

    ranking.sort(key=sort_key)
    top3 = [r for r in ranking if r["status"] == "correct"][:3]

    return {
        "top3": top3,
        "rows": ranking
    }

def _get_player_question_answer(conn, session_id, question_id, player_name):
    if not player_name:
        return None
    row = conn.execute(
        """
        SELECT answer, is_correct, response_ms, score_awarded
        FROM player_answers
        WHERE session_id=? AND question_id=? AND player_name=?
        ORDER BY answer_id ASC
        LIMIT 1
        """,
        (session_id, question_id, player_name)
    ).fetchone()
    return dict(row) if row else None


def ensure_legacy_practice_quiz_row(conn, quiz_id, quiz_name, description):
    """Keep legacy PracticeQuizzes row in sync when old FK still points to it."""
    try:
        table_exists = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name='PracticeQuizzes'"
        ).fetchone()
        if not table_exists:
            return

        conn.execute(
            """
            INSERT OR IGNORE INTO PracticeQuizzes (quiz_id, title, description, created_at)
            VALUES (?, ?, ?, datetime('now'))
            """,
            (quiz_id, quiz_name, description),
        )
        conn.execute(
            "UPDATE PracticeQuizzes SET title=?, description=? WHERE quiz_id=?",
            (quiz_name, description, quiz_id),
        )
    except Exception as e:
        print(f"Warning: could not sync legacy PracticeQuizzes row: {e}")

def migrate_practice_tables():
    """Migrate existing Practice_Quizzes table to include new columns"""
    with get_db_connection() as conn:
        try:
            # Check if Practice_Quizzes table exists
            cursor = conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name='Practice_Quizzes'"
            )
            if cursor.fetchone():
                # Table exists, check if it has the created_by column
                cursor = conn.execute("PRAGMA table_info(Practice_Quizzes)")
                columns = [row[1] for row in cursor.fetchall()]
                if 'practice_id' in columns and 'quiz_id' not in columns:
                    conn.execute("ALTER TABLE Practice_Quizzes RENAME COLUMN practice_id TO quiz_id")
                    cursor = conn.execute("PRAGMA table_info(Practice_Quizzes)")
                    columns = [row[1] for row in cursor.fetchall()]
                if 'title' in columns and 'quiz_name' not in columns:
                    conn.execute("ALTER TABLE Practice_Quizzes RENAME COLUMN title TO quiz_name")
                    cursor = conn.execute("PRAGMA table_info(Practice_Quizzes)")
                    columns = [row[1] for row in cursor.fetchall()]
                
                # Add missing columns
                if 'created_by' not in columns:
                    conn.execute("ALTER TABLE Practice_Quizzes ADD COLUMN created_by INTEGER DEFAULT 1")
                    print("✅ Added created_by column to Practice_Quizzes")
                
                if 'teacher_id' not in columns:
                    conn.execute("ALTER TABLE Practice_Quizzes ADD COLUMN teacher_id INTEGER")
                    conn.execute("UPDATE Practice_Quizzes SET teacher_id = created_by WHERE teacher_id IS NULL")
                if 'created_at' not in columns:
                    conn.execute("ALTER TABLE Practice_Quizzes ADD COLUMN created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP")
                    print("✅ Added created_at column to Practice_Quizzes")
                
                conn.commit()
            
            # Check PracticeQuestions table
            cursor = conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name='PracticeQuestions'"
            )
            if cursor.fetchone():
                cursor = conn.execute("PRAGMA table_info(PracticeQuestions)")
                columns = [row[1] for row in cursor.fetchall()]
                if 'practice_id' in columns and 'quiz_id' not in columns:
                    conn.execute("ALTER TABLE PracticeQuestions RENAME COLUMN practice_id TO quiz_id")
                    cursor = conn.execute("PRAGMA table_info(PracticeQuestions)")
                    columns = [row[1] for row in cursor.fetchall()]
                
                if 'question_type' not in columns:
                    conn.execute("ALTER TABLE PracticeQuestions ADD COLUMN question_type TEXT DEFAULT 'MCQ'")
                    print("✅ Added question_type column to PracticeQuestions")
                
                if 'explanation' not in columns:
                    conn.execute("ALTER TABLE PracticeQuestions ADD COLUMN explanation TEXT")
                    print("✅ Added explanation column to PracticeQuestions")
                
                if 'created_at' not in columns:
                    conn.execute("ALTER TABLE PracticeQuestions ADD COLUMN created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP")
                    print("✅ Added created_at column to PracticeQuestions")
                
                conn.commit()
            
            # Check PracticeOptions table
            cursor = conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name='PracticeOptions'"
            )
            if cursor.fetchone():
                cursor = conn.execute("PRAGMA table_info(PracticeOptions)")
                columns = [row[1] for row in cursor.fetchall()]
                
                if 'option_order' not in columns:
                    conn.execute("ALTER TABLE PracticeOptions ADD COLUMN option_order INTEGER")
                    print("✅ Added option_order column to PracticeOptions")
                
                conn.commit()
            cursor = conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name='PracticeProgress'"
            )
            if cursor.fetchone():
                cursor = conn.execute("PRAGMA table_info(PracticeProgress)")
                columns = [row[1] for row in cursor.fetchall()]
                if 'practice_id' in columns and 'quiz_id' not in columns:
                    conn.execute("ALTER TABLE PracticeProgress RENAME COLUMN practice_id TO quiz_id")
                    conn.commit()
                    columns = [row[1] for row in conn.execute("PRAGMA table_info(PracticeProgress)").fetchall()]

                fk_rows = conn.execute("PRAGMA foreign_key_list(PracticeProgress)").fetchall()
                has_valid_quiz_fk = any(
                    (row[2] == 'Practice_Quizzes' and row[3] == 'quiz_id' and row[4] == 'quiz_id')
                    for row in fk_rows
                )
                if 'quiz_id' in columns and not has_valid_quiz_fk:
                    conn.execute("PRAGMA foreign_keys = OFF")
                    conn.execute("""
                        CREATE TABLE IF NOT EXISTS PracticeProgress_new (
                            progress_id INTEGER PRIMARY KEY AUTOINCREMENT,
                            user_id INTEGER NOT NULL,
                            quiz_id INTEGER NOT NULL,
                            score INTEGER DEFAULT 0,
                            correct_answers INTEGER DEFAULT 0,
                            total_questions INTEGER DEFAULT 0,
                            time_spent INTEGER DEFAULT 0,
                            completed_at TIMESTAMP,
                            started_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                            FOREIGN KEY (user_id) REFERENCES Users(user_id),
                            FOREIGN KEY (quiz_id) REFERENCES Practice_Quizzes(quiz_id),
                            UNIQUE(user_id, quiz_id)
                        )
                    """)
                    conn.execute("""
                        INSERT OR REPLACE INTO PracticeProgress_new
                            (progress_id, user_id, quiz_id, score, correct_answers, total_questions, time_spent, completed_at, started_at)
                        SELECT
                            progress_id, user_id, quiz_id, score, correct_answers, total_questions, time_spent, completed_at, started_at
                        FROM PracticeProgress
                    """)
                    conn.execute("DROP TABLE PracticeProgress")
                    conn.execute("ALTER TABLE PracticeProgress_new RENAME TO PracticeProgress")
                    conn.execute("PRAGMA foreign_keys = ON")
                    conn.commit()
            cursor = conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name='PracticeQuizzes'"
            )
            if cursor.fetchone():
                conn.execute(
                    """
                    INSERT OR IGNORE INTO PracticeQuizzes (quiz_id, title, description, created_at)
                    SELECT quiz_id, quiz_name, COALESCE(description, ''), COALESCE(created_at, datetime('now'))
                    FROM Practice_Quizzes
                    """
                )
                conn.execute(
                    """
                    UPDATE PracticeQuizzes
                    SET
                        title = COALESCE((SELECT pq.quiz_name FROM Practice_Quizzes pq WHERE pq.quiz_id = PracticeQuizzes.quiz_id), title),
                        description = COALESCE((SELECT pq.description FROM Practice_Quizzes pq WHERE pq.quiz_id = PracticeQuizzes.quiz_id), description)
                    WHERE EXISTS (SELECT 1 FROM Practice_Quizzes pq WHERE pq.quiz_id = PracticeQuizzes.quiz_id)
                    """
                )
                conn.commit()
        except Exception as e:
            print(f"✅ Database schema up to date: {e}")

def init_practice_table():
    with get_db_connection() as conn:
        conn.execute("""
        CREATE TABLE IF NOT EXISTS Practice_Quizzes (
            quiz_id INTEGER PRIMARY KEY AUTOINCREMENT,
            quiz_name TEXT NOT NULL,
            description TEXT,
            teacher_id INTEGER,
            created_by INTEGER NOT NULL,
            department TEXT,
            target_departments TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (created_by) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS PracticeQuestions (
            question_id INTEGER PRIMARY KEY AUTOINCREMENT,
            quiz_id INTEGER NOT NULL,
            question_text TEXT NOT NULL,
            question_type TEXT DEFAULT 'MCQ',
            explanation TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (quiz_id) REFERENCES Practice_Quizzes(quiz_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS PracticeOptions (
            option_id INTEGER PRIMARY KEY AUTOINCREMENT,
            question_id INTEGER NOT NULL,
            option_text TEXT NOT NULL,
            is_correct INTEGER DEFAULT 0,
            option_order INTEGER,
            FOREIGN KEY (question_id) REFERENCES PracticeQuestions(question_id)
        )
        """)
        # Progress tracking table
        conn.execute("""
        CREATE TABLE IF NOT EXISTS PracticeProgress (
            progress_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            quiz_id INTEGER NOT NULL,
            score INTEGER DEFAULT 0,
            correct_answers INTEGER DEFAULT 0,
            total_questions INTEGER DEFAULT 0,
            time_spent INTEGER DEFAULT 0,
            completed_at TIMESTAMP,
            started_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id),
            FOREIGN KEY (quiz_id) REFERENCES Practice_Quizzes(quiz_id),
            UNIQUE(user_id, quiz_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS PracticeAnswers (
            answer_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            quiz_id INTEGER NOT NULL,
            question_id INTEGER NOT NULL,
            selected_option_id INTEGER,
            is_correct INTEGER DEFAULT 0,
            submitted_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id),
            FOREIGN KEY (quiz_id) REFERENCES Practice_Quizzes(quiz_id),
            FOREIGN KEY (question_id) REFERENCES PracticeQuestions(question_id),
            FOREIGN KEY (selected_option_id) REFERENCES PracticeOptions(option_id)
        )
        """)
        conn.commit()

# ---------------- DB INIT ----------------
def init_db():
    with get_db_connection() as conn:
        # Users Table
        conn.execute("""
        CREATE TABLE IF NOT EXISTS Users(
            user_id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT NOT NULL,
            email TEXT UNIQUE NOT NULL,
            password TEXT NOT NULL,
            role TEXT NOT NULL,
            department TEXT DEFAULT 'Computer',
            profile_pic TEXT
        )""")
        # Quizzes Table
        conn.execute("""
CREATE TABLE IF NOT EXISTS Quizzes(
    quiz_id INTEGER PRIMARY KEY AUTOINCREMENT,

    quiz_name TEXT NOT NULL,
    description TEXT,

    created_by INTEGER NOT NULL,      -- teacher_id

    subject TEXT,                     -- optional
    quiz_code TEXT UNIQUE,            -- practice join code

    mode TEXT DEFAULT 'practice',     -- 'practice' or 'live'

    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (created_by) REFERENCES Users(user_id)
)
""")

        # Questions Table
        conn.execute("""
CREATE TABLE IF NOT EXISTS Questions(
    question_id INTEGER PRIMARY KEY AUTOINCREMENT,

    quiz_id INTEGER NOT NULL,

    question_text TEXT NOT NULL,

    question_type TEXT DEFAULT 'MCQ',

    time_limit INTEGER DEFAULT 30,          -- live quiz timer

    marks INTEGER DEFAULT 10,               -- score per question

    explanation TEXT,                       -- practice mode explanation

    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,

    FOREIGN KEY (quiz_id) REFERENCES Quizzes(quiz_id)
)
""")

        # Options Table
        conn.execute("""
CREATE TABLE IF NOT EXISTS Options(
    option_id INTEGER PRIMARY KEY AUTOINCREMENT,

    question_id INTEGER NOT NULL,

    option_text TEXT NOT NULL,

    is_correct INTEGER DEFAULT 0,   -- 0 = wrong, 1 = correct

    option_order INTEGER,           -- display order (A,B,C,D)

    FOREIGN KEY (question_id) REFERENCES Questions(question_id)
)
""")

        # GameSessions Table
        conn.execute("""
        CREATE TABLE IF NOT EXISTS GameSessions(
            session_id INTEGER PRIMARY KEY AUTOINCREMENT,
            quiz_id INTEGER,
            game_pin INTEGER UNIQUE,
            start_time DATETIME DEFAULT CURRENT_TIMESTAMP,
            end_time DATETIME,
            FOREIGN KEY (quiz_id) REFERENCES Quizzes(quiz_id)
        )""")
        # PlayerScores Table
        conn.execute("""
        CREATE TABLE IF NOT EXISTS PlayerScores(
            score_id INTEGER PRIMARY KEY AUTOINCREMENT,
            session_id INTEGER,
            user_id INTEGER,
            score INTEGER DEFAULT 0,
            correct_answers INTEGER DEFAULT 0,
            time_taken INTEGER DEFAULT 0,
            FOREIGN KEY (session_id) REFERENCES GameSessions(session_id),
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )""")

        # ---------------- Live Sessions Table ----------------
        conn.execute("""
        CREATE TABLE IF NOT EXISTS live_sessions (
    session_id INTEGER PRIMARY KEY AUTOINCREMENT,
    quiz_id INTEGER NOT NULL,
    pin INTEGER UNIQUE NOT NULL,
    is_active INTEGER DEFAULT 1,
    created_by INTEGER,
    start_time DATETIME DEFAULT NULL,
    current_question INTEGER DEFAULT 0,
    started INTEGER DEFAULT 0,
    question_started_at DATETIME DEFAULT NULL,
    FOREIGN KEY (quiz_id) REFERENCES Quizzes(quiz_id),
    FOREIGN KEY (created_by) REFERENCES Users(user_id)
)
""")

        # ---------------- Participants Table ----------------
        conn.execute("""
        CREATE TABLE IF NOT EXISTS participants (
            participant_id INTEGER PRIMARY KEY AUTOINCREMENT,
            session_id INTEGER NOT NULL,
            nickname TEXT NOT NULL,
            joined_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (session_id) REFERENCES live_sessions(session_id)
        )""")

        conn.execute("""
        CREATE TABLE IF NOT EXISTS player_answers (
    answer_id INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id INTEGER NOT NULL,
    question_id INTEGER,
    question_index INTEGER DEFAULT 0,
    player_name TEXT NOT NULL,
    answer TEXT NOT NULL,
    is_correct INTEGER DEFAULT 0,
    response_ms INTEGER DEFAULT 0,
    score_awarded INTEGER DEFAULT 0,
    submitted_at DATETIME DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (session_id) REFERENCES live_sessions(session_id)
)

""")
        conn.execute("""
        CREATE TABLE IF NOT EXISTS DailyTips(
            tip_id INTEGER PRIMARY KEY AUTOINCREMENT,
            content_text TEXT NOT NULL,
            content_type TEXT NOT NULL,
            subject TEXT DEFAULT 'general',
            difficulty_level TEXT DEFAULT 'beginner',
            language TEXT DEFAULT 'en',
            is_active INTEGER DEFAULT 1,
            publish_date DATE,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS UserTipViews(
            view_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            tip_id INTEGER NOT NULL,
            viewed_on DATE NOT NULL,
            reward_points INTEGER DEFAULT 0,
            viewed_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(user_id, viewed_on),
            FOREIGN KEY (user_id) REFERENCES Users(user_id),
            FOREIGN KEY (tip_id) REFERENCES DailyTips(tip_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS StudyNotes(
            note_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            content TEXT NOT NULL,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            updated_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS Flashcards(
            card_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            front_text TEXT NOT NULL,
            back_text TEXT NOT NULL,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS DailyGoals(
            goal_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            goal_text TEXT NOT NULL,
            target_date DATE,
            is_completed INTEGER DEFAULT 0,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS StudyJournal(
            journal_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            study_date DATE NOT NULL,
            minutes_spent INTEGER DEFAULT 0,
            topics TEXT,
            notes TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS ResourceLibrary(
            resource_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            resource_type TEXT DEFAULT 'link',
            url TEXT NOT NULL,
            description TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS StudyReminders(
            reminder_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            due_date DATE,
            is_done INTEGER DEFAULT 0,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS MindMaps(
            map_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            central_topic TEXT NOT NULL,
            related_topics TEXT NOT NULL,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            updated_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS SelfAssessment(
            assessment_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            topic_name TEXT NOT NULL,
            status TEXT DEFAULT 'learning',
            notes TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            updated_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS PomodoroLogs(
            log_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            focus_minutes INTEGER DEFAULT 25,
            break_minutes INTEGER DEFAULT 5,
            cycles_completed INTEGER DEFAULT 1,
            logged_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES Users(user_id)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS PracticeFirstAttempts(
            attempt_id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            quiz_id INTEGER NOT NULL,
            score INTEGER DEFAULT 0,
            correct_answers INTEGER DEFAULT 0,
            total_questions INTEGER DEFAULT 0,
            attempted_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(user_id, quiz_id),
            FOREIGN KEY (user_id) REFERENCES Users(user_id),
            FOREIGN KEY (quiz_id) REFERENCES Practice_Quizzes(quiz_id)
        )
        """)
        # Keep only the earliest stored first-attempt row per student+quiz,
        # then enforce uniqueness for legacy databases that may have duplicates.
        conn.execute("""
            DELETE pfa
            FROM PracticeFirstAttempts pfa
            JOIN (
                SELECT user_id, quiz_id, MIN(attempt_id) AS keep_id
                FROM PracticeFirstAttempts
                GROUP BY user_id, quiz_id
            ) kept
                ON pfa.user_id = kept.user_id
                AND pfa.quiz_id = kept.quiz_id
            WHERE pfa.attempt_id <> kept.keep_id
        """)
        conn.execute("""
            CREATE UNIQUE INDEX IF NOT EXISTS idx_practice_first_attempt_unique
            ON PracticeFirstAttempts(user_id, quiz_id)
        """)
        live_session_columns = [row[1] for row in conn.execute("PRAGMA table_info(live_sessions)").fetchall()]
        if 'started' not in live_session_columns:
            conn.execute("ALTER TABLE live_sessions ADD COLUMN started INTEGER DEFAULT 0")
        if 'question_started_at' not in live_session_columns:
            conn.execute("ALTER TABLE live_sessions ADD COLUMN question_started_at DATETIME DEFAULT NULL")

        answer_columns = [row[1] for row in conn.execute("PRAGMA table_info(player_answers)").fetchall()]
        if 'question_id' not in answer_columns:
            conn.execute("ALTER TABLE player_answers ADD COLUMN question_id INTEGER")
        if 'question_index' not in answer_columns:
            conn.execute("ALTER TABLE player_answers ADD COLUMN question_index INTEGER DEFAULT 0")
        if 'is_correct' not in answer_columns:
            conn.execute("ALTER TABLE player_answers ADD COLUMN is_correct INTEGER DEFAULT 0")
        if 'response_ms' not in answer_columns:
            conn.execute("ALTER TABLE player_answers ADD COLUMN response_ms INTEGER DEFAULT 0")
        if 'score_awarded' not in answer_columns:
            conn.execute("ALTER TABLE player_answers ADD COLUMN score_awarded INTEGER DEFAULT 0")
        # Backward-compatible schema updates
        user_columns = [row[1] for row in conn.execute("PRAGMA table_info(Users)").fetchall()]
        if 'department' not in user_columns:
            conn.execute("ALTER TABLE Users ADD COLUMN department TEXT DEFAULT 'Computer'")
            conn.execute("UPDATE Users SET department='Computer' WHERE department IS NULL OR department=''")
        if 'theme_mode' not in user_columns:
            conn.execute("ALTER TABLE Users ADD COLUMN theme_mode TEXT DEFAULT 'light'")
        if 'font_scale' not in user_columns:
            conn.execute("ALTER TABLE Users ADD COLUMN font_scale TEXT DEFAULT 'medium'")
        if 'app_language' not in user_columns:
            conn.execute("ALTER TABLE Users ADD COLUMN app_language TEXT DEFAULT 'en'")
        if 'email_alerts' not in user_columns:
            conn.execute("ALTER TABLE Users ADD COLUMN email_alerts INTEGER DEFAULT 1")
        if 'mute_notifications' not in user_columns:
            conn.execute("ALTER TABLE Users ADD COLUMN mute_notifications INTEGER DEFAULT 0")
        if 'session_version' not in user_columns:
            conn.execute("ALTER TABLE Users ADD COLUMN session_version INTEGER DEFAULT 0")

        practice_table_exists = conn.execute(
            "SELECT 1 FROM sqlite_master WHERE type='table' AND name='Practice_Quizzes'"
        ).fetchone()
        if practice_table_exists:
            practice_quiz_columns = [row[1] for row in conn.execute("PRAGMA table_info(Practice_Quizzes)").fetchall()]
            if 'department' not in practice_quiz_columns:
                conn.execute("ALTER TABLE Practice_Quizzes ADD COLUMN department TEXT")
            conn.execute("""
                UPDATE Practice_Quizzes
                SET department = (
                    SELECT COALESCE(NULLIF(u.department, ''), 'Computer')
                    FROM Users u
                    WHERE u.user_id = Practice_Quizzes.created_by
                )
                WHERE department IS NULL OR department = ''
            """)

            if 'target_departments' not in practice_quiz_columns:
                conn.execute("ALTER TABLE Practice_Quizzes ADD COLUMN target_departments TEXT")
            conn.execute("""
                UPDATE Practice_Quizzes
                SET target_departments = COALESCE(NULLIF(department, ''), 'Computer')
                WHERE target_departments IS NULL OR target_departments = ''
            """)

        tip_view_columns = [row[1] for row in conn.execute("PRAGMA table_info(UserTipViews)").fetchall()]
        if 'reward_points' not in tip_view_columns:
            conn.execute("ALTER TABLE UserTipViews ADD COLUMN reward_points INTEGER DEFAULT 0")

        # Prevent duplicate live joins and duplicate answer submissions.
        # Clean legacy duplicate rows first so unique indexes can be created safely.
        try:
            conn.execute("""
                DELETE FROM participants
                WHERE participant_id NOT IN (
                    SELECT MIN(participant_id)
                    FROM participants
                    GROUP BY session_id, nickname
                )
            """)
        except Exception:
            pass

        try:
            conn.execute("""
                DELETE FROM player_answers
                WHERE answer_id NOT IN (
                    SELECT MIN(answer_id)
                    FROM player_answers
                    WHERE question_id IS NOT NULL
                    GROUP BY session_id, question_id, player_name
                )
                AND question_id IS NOT NULL
            """)
        except Exception:
            pass

        conn.execute("""
            CREATE UNIQUE INDEX IF NOT EXISTS uq_participants_session_nickname
            ON participants(session_id, nickname)
        """)
        conn.execute("""
            CREATE UNIQUE INDEX IF NOT EXISTS uq_player_answers_once
            ON player_answers(session_id, question_id, player_name)
            WHERE question_id IS NOT NULL
        """)

        tip_count = conn.execute("SELECT COUNT(*) AS c FROM DailyTips").fetchone()["c"]
        if tip_count == 0:
            sample_tips = [
                ("Did you know honey never spoils?", "fact", "general", "beginner", "en"),
                ("When you learn a new term, use it once in a sentence for better memory.", "life_hack", "general", "beginner", "en"),
                ("Break a large problem into smaller steps before solving.", "tip", "general", "beginner", "en"),
                ("Revision after 24 hours improves long-term retention.", "tip", "general", "intermediate", "en"),
                ("Prime numbers are numbers greater than 1 with exactly two factors.", "fact", "math", "beginner", "en"),
                ("In physics, acceleration is change in velocity per unit time.", "fact", "science", "beginner", "en"),
                ("Use active voice in most English sentences for clarity.", "tip", "grammar", "beginner", "en"),
                ("आज का विचार: छोटे-छोटे निरंतर प्रयास बड़ी सफलता बनाते हैं।", "quote", "general", "beginner", "hi"),
                ("मराठी टिप: नवीन शब्द लक्षात ठेवायचा असेल तर तो वाक्यात वापरा.", "tip", "general", "beginner", "mr"),
                ("Practice spaced repetition: revisit difficult topics at increasing intervals.", "tip", "general", "advanced", "en"),
                ("Reward yourself after completing a focused 25-minute study sprint.", "life_hack", "general", "beginner", "en"),
                ("Science fact: Water expands when it freezes, unlike most liquids.", "fact", "science", "intermediate", "en")
            ]
            conn.executemany("""
                INSERT INTO DailyTips (content_text, content_type, subject, difficulty_level, language, is_active, publish_date)
                VALUES (?, ?, ?, ?, ?, 1, date('now'))
            """, sample_tips)

        multilingual_tips = [
            ("हिंदी टिप: नया कॉन्सेप्ट सीखने के बाद उसे किसी दोस्त को समझाकर देखें।", "tip", "general", "beginner", "hi"),
            ("हिंदी तथ्य: मानव मस्तिष्क नींद के दौरान यादों को मजबूत करता है।", "fact", "science", "intermediate", "hi"),
            ("हिंदी जीवन मंत्र: कठिन काम को 10 मिनट के छोटे हिस्सों में शुरू करें।", "life_hack", "general", "beginner", "hi"),
            ("मराठी तथ्य: मध योग्यरीत्या साठवला तर तो दीर्घकाळ खराब होत नाही.", "fact", "general", "beginner", "mr"),
            ("मराठी अभ्यास टिप: २५ मिनिटे लक्ष केंद्रित करून अभ्यास करा, मग ५ मिनिटे विश्रांती घ्या.", "life_hack", "general", "beginner", "mr"),
            ("मराठी प्रेरणा: रोज थोडी प्रगती केली तरी मोठा बदल घडतो.", "quote", "general", "beginner", "mr")
        ]
        for tip in multilingual_tips:
            exists = conn.execute(
                "SELECT 1 FROM DailyTips WHERE content_text=? LIMIT 1",
                (tip[0],)
            ).fetchone()
            if not exists:
                conn.execute("""
                    INSERT INTO DailyTips (content_text, content_type, subject, difficulty_level, language, is_active, publish_date)
                    VALUES (?, ?, ?, ?, ?, 1, date('now'))
                """, tip)


init_db()

# ---------------- PASSWORD CHECK ----------------
def is_password_strong(p):
    return len(p) >= 8 and any(c.isalpha() for c in p) and any(c.isdigit() for c in p) and any(c in "!@#$%^&*" for c in p)

def normalize_departments(departments):
    selected = []
    for dept in departments:
        value = (dept or "").strip()
        if value in DEPARTMENTS and value not in selected:
            selected.append(value)
    return selected

def slugify_filename(value):
    safe = re.sub(r'[^A-Za-z0-9._-]+', '_', (value or "").strip())
    return safe.strip("._-") or "quiz"

def _require_student():
    if 'user_id' not in session or session.get('role') != 'Student':
        flash("Please login as student")
        return False
    return True

def _determine_tip_subject(conn, user_id, role):
    if role == "Teacher":
        row = conn.execute("""
            SELECT COALESCE(NULLIF(subject, ''), 'general') AS subject, COUNT(*) AS c
            FROM Quizzes
            WHERE created_by=?
            GROUP BY subject
            ORDER BY c DESC, subject ASC
            LIMIT 1
        """, (user_id,)).fetchone()
        return (row["subject"] if row else "general") or "general"

    # Older DBs may not have Practice_Quizzes.subject, so keep this backward-compatible.
    practice_cols = {row[1] for row in conn.execute("PRAGMA table_info(Practice_Quizzes)").fetchall()}
    if "subject" not in practice_cols:
        return "general"

    try:
        row = conn.execute("""
            SELECT COALESCE(NULLIF(p.subject, ''), 'general') AS subject, COUNT(*) AS c
            FROM PracticeProgress pp
            JOIN Practice_Quizzes p ON p.quiz_id = pp.quiz_id
            WHERE pp.user_id=?
            GROUP BY subject
            ORDER BY c DESC, subject ASC
            LIMIT 1
        """, (user_id,)).fetchone()
        return (row["subject"] if row else "general") or "general"
    except mysql.connector.Error:
        return "general"

def _difficulty_for_user(conn, user_id):
    row = conn.execute(
        "SELECT COUNT(*) AS views FROM UserTipViews WHERE user_id=?",
        (user_id,)
    ).fetchone()
    views = row["views"] if row else 0
    if views < 7:
        return "beginner"
    if views < 21:
        return "intermediate"
    return "advanced"

def _pick_rotating_tip(rows):
    if not rows:
        return None
    day_index = int(datetime.datetime.utcnow().strftime("%j"))
    return rows[day_index % len(rows)]

def _calculate_tip_streak(conn, user_id):
    rows = conn.execute("""
        SELECT viewed_on
        FROM UserTipViews
        WHERE user_id=?
        ORDER BY viewed_on DESC
    """, (user_id,)).fetchall()
    if not rows:
        return 0

    streak = 0
    expected_date = datetime.date.today()
    for row in rows:
        viewed_date = datetime.date.fromisoformat(row["viewed_on"])
        if viewed_date == expected_date:
            streak += 1
            expected_date = expected_date - datetime.timedelta(days=1)
        elif viewed_date > expected_date:
            continue
        else:
            break
    return streak

def get_daily_tip_for_user(conn, user_id, role, language="en"):
    preferred_language = (language or "en").strip().lower()
    if preferred_language not in ("en", "hi", "mr"):
        preferred_language = "en"

    subject = _determine_tip_subject(conn, user_id, role)
    difficulty = _difficulty_for_user(conn, user_id)

    candidate_rows = conn.execute("""
        SELECT *
        FROM DailyTips
        WHERE is_active=1
          AND language=?
          AND difficulty_level=?
          AND (subject=? OR subject='general')
        ORDER BY tip_id ASC
    """, (preferred_language, difficulty, subject)).fetchall()
    tip = _pick_rotating_tip(candidate_rows)

    if not tip:
        fallback = conn.execute("""
            SELECT *
            FROM DailyTips
            WHERE is_active=1 AND language=?
            ORDER BY tip_id ASC
        """, (preferred_language,)).fetchall()
        tip = _pick_rotating_tip(fallback)

    if not tip and preferred_language != "en":
        fallback_en = conn.execute("""
            SELECT *
            FROM DailyTips
            WHERE is_active=1 AND language='en'
            ORDER BY tip_id ASC
        """).fetchall()
        tip = _pick_rotating_tip(fallback_en)

    if not tip:
        any_tip = conn.execute("""
            SELECT *
            FROM DailyTips
            WHERE is_active=1
            ORDER BY tip_id ASC
        """).fetchall()
        tip = _pick_rotating_tip(any_tip)

    return tip, subject, difficulty, preferred_language

# ---------------- LOGIN REQUIRED DECORATOR ----------------
from functools import wraps

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'user_id' not in session:
            flash("Please login first")
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

def _valid_email(email):
    value = (email or "").strip()
    return bool(re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", value))

def _to_int_flag(raw_value):
    return 1 if str(raw_value).strip().lower() in ("1", "true", "on", "yes") else 0

def _delete_user_account(conn, user_id):
    quiz_ids = [row["quiz_id"] for row in conn.execute(
        "SELECT quiz_id FROM Quizzes WHERE created_by=?",
        (user_id,)
    ).fetchall()]
    for quiz_id in quiz_ids:
        live_session_ids = [row["session_id"] for row in conn.execute(
            "SELECT session_id FROM live_sessions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchall()]
        for sid in live_session_ids:
            conn.execute("DELETE FROM participants WHERE session_id=?", (sid,))
            conn.execute("DELETE FROM player_answers WHERE session_id=?", (sid,))
        conn.execute("DELETE FROM live_sessions WHERE quiz_id=?", (quiz_id,))

        game_session_ids = [row["session_id"] for row in conn.execute(
            "SELECT session_id FROM GameSessions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchall()]
        for sid in game_session_ids:
            conn.execute("DELETE FROM PlayerScores WHERE session_id=?", (sid,))
        conn.execute("DELETE FROM GameSessions WHERE quiz_id=?", (quiz_id,))

        question_ids = [row["question_id"] for row in conn.execute(
            "SELECT question_id FROM Questions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchall()]
        for qid in question_ids:
            conn.execute("DELETE FROM Options WHERE question_id=?", (qid,))
        conn.execute("DELETE FROM Questions WHERE quiz_id=?", (quiz_id,))
        conn.execute("DELETE FROM Quizzes WHERE quiz_id=?", (quiz_id,))

    practice_quiz_ids = [row["quiz_id"] for row in conn.execute(
        "SELECT quiz_id FROM Practice_Quizzes WHERE created_by=?",
        (user_id,)
    ).fetchall()]
    for quiz_id in practice_quiz_ids:
        practice_question_ids = [row["question_id"] for row in conn.execute(
            "SELECT question_id FROM PracticeQuestions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchall()]
        for qid in practice_question_ids:
            conn.execute("DELETE FROM PracticeOptions WHERE question_id=?", (qid,))
        conn.execute("DELETE FROM PracticeQuestions WHERE quiz_id=?", (quiz_id,))
        conn.execute("DELETE FROM PracticeAnswers WHERE quiz_id=?", (quiz_id,))
        conn.execute("DELETE FROM PracticeProgress WHERE quiz_id=?", (quiz_id,))
        conn.execute("DELETE FROM Practice_Quizzes WHERE quiz_id=?", (quiz_id,))

        legacy_exists = conn.execute(
            "SELECT 1 FROM sqlite_master WHERE type='table' AND name='PracticeQuizzes'"
        ).fetchone()
        if legacy_exists:
            conn.execute("DELETE FROM PracticeQuizzes WHERE quiz_id=?", (quiz_id,))

    conn.execute("DELETE FROM PracticeAnswers WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM PracticeProgress WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM UserTipViews WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM PlayerScores WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM StudyNotes WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM Flashcards WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM DailyGoals WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM StudyJournal WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM ResourceLibrary WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM StudyReminders WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM MindMaps WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM SelfAssessment WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM PomodoroLogs WHERE user_id=?", (user_id,))
    conn.execute("DELETE FROM Users WHERE user_id=?", (user_id,))

@app.before_request
def _enforce_login_session_version():
    if request.endpoint == 'static':
        return None
    if 'user_id' not in session:
        return None

    user_id = session.get('user_id')
    with get_db_connection() as conn:
        user = conn.execute(
            """
            SELECT user_id, username, role, department, session_version,
                   theme_mode, font_scale, app_language,
                   email_alerts, mute_notifications
            FROM Users
            WHERE user_id=?
            """,
            (user_id,)
        ).fetchone()

    if not user:
        session.clear()
        flash("Account not found. Please login again.")
        return redirect(url_for('login'))

    db_session_version = user["session_version"] or 0
    if session.get("session_version", db_session_version) != db_session_version:
        session.clear()
        flash("You were logged out because account sessions were reset.")
        return redirect(url_for('login'))

    session['username'] = user['username']
    session['role'] = user['role']
    session['department'] = user['department'] or 'Computer'
    session['session_version'] = db_session_version
    session['theme_mode'] = user['theme_mode'] or 'light'
    session['font_scale'] = user['font_scale'] or 'medium'
    session['app_language'] = user['app_language'] or 'en'
    session['email_alerts'] = 1 if (user['email_alerts'] or 0) else 0
    session['mute_notifications'] = 1 if (user['mute_notifications'] or 0) else 0


# ---------------- HELPER FUNCTION ----------------
def get_teacher_quizzes(user_id):
    with get_db_connection() as conn:
        quizzes = conn.execute("SELECT * FROM Quizzes WHERE created_by=?", (user_id,)).fetchall()
    return quizzes

# ---------------- LOGIN ----------------
@app.route('/', methods=['GET', 'POST'])
@app.route('/login', methods=['GET', 'POST'])
def login():
    locked = False  # optional: future use for account lock
    if request.method == 'POST':
        email = request.form['email']
        password = request.form['password']

        with get_db_connection() as conn:
            user = conn.execute("SELECT * FROM Users WHERE email=?", (email,)).fetchone()

        if user and check_password_hash(user['password'], password):
            session['user_id'] = user['user_id']
            session['username'] = user['username']
            session['role'] = user['role']
            session['department'] = (user['department'] or 'Computer') if 'department' in user.keys() else 'Computer'
            session['session_version'] = (user['session_version'] or 0) if 'session_version' in user.keys() else 0
            session['theme_mode'] = (user['theme_mode'] or 'light') if 'theme_mode' in user.keys() else 'light'
            session['font_scale'] = (user['font_scale'] or 'medium') if 'font_scale' in user.keys() else 'medium'
            session['app_language'] = (user['app_language'] or 'en') if 'app_language' in user.keys() else 'en'
            session['tip_language'] = session['app_language']
            session['email_alerts'] = 1 if ((user['email_alerts'] if 'email_alerts' in user.keys() else 1) or 0) else 0
            session['mute_notifications'] = 1 if ((user['mute_notifications'] if 'mute_notifications' in user.keys() else 0) or 0) else 0
            return redirect('/teacher_dashboard' if user['role'] == "Teacher" else '/student_dashboard')

        flash("Invalid login")

    return render_template('auth/login.html', locked=locked)

# ---------------- REGISTER ----------------
@app.route('/register', methods=['GET', 'POST'])
def register():
    if request.method == 'POST':
        username = request.form['username']
        email = request.form['email']
        password = request.form['password']
        role = request.form['role']
        department = (request.form.get('department') or '').strip()
        captcha = request.form.get('captcha')

        if role == "Student":
            if department not in DEPARTMENTS:
                flash("Student sathi valid department select kara")
                return redirect('/register')
        else:
            department = None

        # CAPTCHA validation (optional)
        if captcha and int(captcha) != session.get('captcha_answer'):
            flash("Incorrect CAPTCHA")
            return redirect('/register')

        # Password strength check
        if not is_password_strong(password):
            flash("Weak password")
            return redirect('/register')

        # Insert into DB
        try:
            with get_db_connection() as conn:
                conn.execute(
                    "INSERT INTO Users(username,email,password,role,department) VALUES(?,?,?,?,?)",
                    (username, email, generate_password_hash(password), role, department)
                )
                conn.commit()
            flash("Registered successfully")
            return redirect('/login')
        except:
            flash("Email already exists")
            return redirect('/register')

    # GET request → generate captcha numbers
    questions = ["Your first pet's name?", "Favorite color?", "Mother's maiden name?"]
    a, b = 4, 7  # example
    session['captcha_answer'] = a + b
    return render_template('auth/register.html', questions=questions, a=a, b=b)


# ---------- CREATE PRACTICE QUIZ ----------
@app.route("/create_practice_quiz", methods=["GET", "POST"])
@login_required
def create_practice_quiz():
    if request.method == "POST":
        try:
            title = request.form.get('title')
            description = request.form.get('description', '')
            created_by = session['user_id']
            selected_departments = normalize_departments(request.form.getlist('departments'))
            print(f"DEBUG: title={title}, created_by={created_by}")

            # Get all questions and options from form FIRST
            questions = request.form.getlist("question_text[]")
            explanations = request.form.getlist("explanation[]")
            print(f"DEBUG: Questions received: {len(questions)} questions")
            print(f"DEBUG: Explanations: {len(explanations)}")

            if not questions:
                flash("Please add at least one question", "danger")
                return redirect(url_for("create_practice_quiz"))
            if not selected_departments:
                flash("Please select at least one department", "danger")
                return redirect(url_for("create_practice_quiz"))

            with get_db_connection() as conn:
                cursor = conn.cursor()

                # Insert quiz
                print(f"DEBUG: Inserting quiz: quiz_name={title}, created_by={created_by}")
                cursor.execute("""
                    INSERT INTO Practice_Quizzes (quiz_name, description, created_by, teacher_id, target_departments)
                    VALUES (?, ?, ?, ?, ?)
                """, (title, description, created_by, created_by, ",".join(selected_departments)))
                quiz_id = cursor.lastrowid
                print(f"DEBUG: Created quiz with ID: {quiz_id}")
                ensure_legacy_practice_quiz_row(conn, quiz_id, title, description)

                # Insert all questions and options
                for idx, q_text in enumerate(questions):
                    explanation = explanations[idx] if idx < len(explanations) else ""
                    print(f"DEBUG: Inserting question {idx}: {q_text}")
                    
                    cursor.execute("""
                        INSERT INTO PracticeQuestions (quiz_id, question_text, explanation)
                        VALUES (?, ?, ?)
                    """, (quiz_id, q_text, explanation))
                    question_id = cursor.lastrowid
                    print(f"DEBUG: Created question ID: {question_id}")

                    # Get the correct option for this question
                    correct_option = request.form.get(f"correct_option_{idx}", "A")
                    print(f"DEBUG: Correct option for question {idx}: {correct_option}")

                    # Insert options for this question
                    for opt_label in ["A", "B", "C", "D"]:
                        opt_text = request.form.get(f"option_{opt_label}_{idx}")
                        is_correct = 1 if correct_option == opt_label else 0
                        print(f"DEBUG: Option {opt_label}: is_correct={is_correct}, text={opt_text}")
                        
                        if opt_text:  # Only insert if option text is provided
                            opt_order = ord(opt_label) - ord('A')  # Convert A,B,C,D to 0,1,2,3
                            cursor.execute("""
                                INSERT INTO PracticeOptions (question_id, option_text, is_correct, option_order)
                                VALUES (?, ?, ?, ?)
                            """, (question_id, opt_text, is_correct, opt_order))

                print("DEBUG: Transaction committed successfully (via context manager)")

            flash("Practice Quiz created successfully! ✅", "success")
            return redirect(url_for("list_practice_quizzes"))
            
        except Exception as e:
            print(f"ERROR in create_practice_quiz: {type(e).__name__}: {e}")
            import traceback
            traceback.print_exc()
            flash(f"Error: {str(e)}", "danger")
            return redirect(url_for("create_practice_quiz"))

    return render_template("teacher/create_practice_quiz.html")


# ---------- LIST PRACTICE QUIZZES ----------
@app.route("/list_practice_quizzes", methods=["GET"])
@login_required
def list_practice_quizzes():
    if session.get('role') != 'Teacher':
        return redirect('/login')
    
    with get_db_connection() as conn:
        quizzes = conn.execute("""
            SELECT p.*, COUNT(pq.question_id) AS question_count
            FROM Practice_Quizzes p
            LEFT JOIN PracticeQuestions pq ON p.quiz_id = pq.quiz_id
            WHERE p.created_by = ?
            GROUP BY p.quiz_id
            ORDER BY p.quiz_id DESC
        """, (session['user_id'],)).fetchall()
    
    return render_template('teacher/list_practice_quizzes.html', quizzes=quizzes)


# ---------- OPEN/VIEW PRACTICE QUIZ ----------
@app.route("/open_practice_quiz/<int:quiz_id>", methods=["GET"])
@login_required
def open_practice_quiz(quiz_id):
    if session.get('role') != 'Teacher':
        return redirect('/login')
    
    with get_db_connection() as conn:
        quiz = conn.execute(
            "SELECT * FROM Practice_Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('list_practice_quizzes'))
        
        questions = conn.execute(
            "SELECT * FROM PracticeQuestions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchall()
        
        questions_with_options = []
        for q in questions:
            options = conn.execute(
                "SELECT * FROM PracticeOptions WHERE question_id=?",
                (q['question_id'],)
            ).fetchall()
            questions_with_options.append({
                "question": q,
                "options": options
            })
    
    return render_template(
        'teacher/open_practice_quiz.html',
        quiz=quiz,
        questions=questions_with_options
    )


# ---------- EDIT PRACTICE QUIZ ----------
@app.route("/edit_practice_quiz/<int:quiz_id>", methods=["GET", "POST"])
@login_required
def edit_practice_quiz(quiz_id):
    if session.get('role') != 'Teacher':
        return redirect('/login')
    
    with get_db_connection() as conn:
        quiz = conn.execute(
            "SELECT * FROM Practice_Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('list_practice_quizzes'))
        
        if request.method == 'POST':
            print(f"DEBUG: Form data keys: {list(request.form.keys())}")
            print(f"DEBUG: Quiz ID: {quiz_id}")
            print(f"DEBUG: Existing question IDs: {request.form.getlist('existing_question_id[]')}")
            print(f"DEBUG: New question texts: {request.form.getlist('new_question_text[]')}")
            
            # Update quiz metadata
            title = request.form.get('title', quiz['quiz_name'])
            description = request.form.get('description', quiz['description'] or '')
            conn.execute(
                "UPDATE Practice_Quizzes SET quiz_name=?, description=? WHERE quiz_id=?",
                (title, description, quiz_id)
            )
            ensure_legacy_practice_quiz_row(conn, quiz_id, title, description)
            
            # Update existing questions
            existing_ids = request.form.getlist('existing_question_id[]')
            question_texts = request.form.getlist('question_text[]')
            explanations = request.form.getlist('explanation[]')
            
            if existing_ids:
                print(f"DEBUG: Updating {len(existing_ids)} existing questions")
                
                for idx, q_id in enumerate(existing_ids):
                    q_id = int(q_id)
                    q_text = question_texts[idx] if idx < len(question_texts) else ''
                    explanation = explanations[idx] if idx < len(explanations) else ''
                    
                    print(f"DEBUG: Updating question {q_id}: {q_text}")
                    
                    # Get correct answer letter from radio button
                    correct_letter = request.form.get(f'correct_option_{q_id}', 'A')
                    correct_index = ord(correct_letter) - ord('A')
                    
                    # Update question
                    conn.execute(
                        "UPDATE PracticeQuestions SET question_text=?, explanation=? WHERE question_id=?",
                        (q_text, explanation, q_id)
                    )
                    
                    # Get and update options
                    option_texts = request.form.getlist(f'option_text_{q_id}[]')
                    existing_options = conn.execute(
                        "SELECT option_id FROM PracticeOptions WHERE question_id=? ORDER BY option_order",
                        (q_id,)
                    ).fetchall()
                    
                    for opt_idx, opt_text in enumerate(option_texts):
                        is_correct = 1 if opt_idx == correct_index else 0
                        if opt_idx < len(existing_options):
                            conn.execute(
                                "UPDATE PracticeOptions SET option_text=?, is_correct=?, option_order=? WHERE option_id=?",
                                (opt_text, is_correct, opt_idx, existing_options[opt_idx]['option_id'])
                            )
                        else:
                            conn.execute(
                                "INSERT INTO PracticeOptions (question_id, option_text, is_correct, option_order) VALUES (?, ?, ?, ?)",
                                (q_id, opt_text, is_correct, opt_idx)
                            )
                    # If user reduced options, remove extras from DB
                    if len(existing_options) > len(option_texts):
                        for extra in existing_options[len(option_texts):]:
                            conn.execute(
                                "DELETE FROM PracticeOptions WHERE option_id=?",
                                (extra['option_id'],)
                            )
            
            # Add new questions
            new_question_texts = request.form.getlist('new_question_text[]')
            new_explanations = request.form.getlist('new_explanation[]')
            
            print(f"DEBUG: New questions count: {len(new_question_texts)}")
            print(f"DEBUG: New question texts: {new_question_texts}")
            
            # Verify quiz still exists before inserting new questions
            quiz_check = conn.execute(
                "SELECT quiz_id FROM Practice_Quizzes WHERE quiz_id=?",
                (quiz_id,)
            ).fetchone()
            print(f"DEBUG: Quiz {quiz_id} exists: {quiz_check is not None}")
            
            if not quiz_check:
                flash("Quiz not found after update. Changes may not have been saved.")
                return redirect(url_for('list_practice_quizzes'))
            
            # Only process new questions if there are any
            if new_question_texts and any(q.strip() for q in new_question_texts):
                new_correct_keys = [
                    field_key for field_key in request.form.keys()
                    if field_key.startswith('new_correct_')
                ]
                
                # Process each new question
                for idx, q_text in enumerate(new_question_texts):
                    if q_text.strip():  # Only if question text is not empty
                        explanation = new_explanations[idx] if idx < len(new_explanations) else ''
                        
                        print(f"DEBUG: Inserting new question {idx}: {q_text}, quiz_id={quiz_id}")
                        
                        try:
                            # Insert question
                            cursor = conn.execute(
                                "INSERT INTO PracticeQuestions (quiz_id, question_text, explanation, created_at) VALUES (?, ?, ?, datetime('now'))",
                                (quiz_id, q_text, explanation)
                            )
                            question_id = cursor.lastrowid
                            print(f"DEBUG: Question inserted successfully with ID: {question_id}")
                            
                            # Map question fields by generated timestamp suffix
                            correct_letter = 'A'
                            option_texts = []
                            if idx < len(new_correct_keys):
                                correct_key = new_correct_keys[idx]
                                timestamp = correct_key.replace('new_correct_', '')
                                correct_letter = request.form.get(correct_key, 'A')
                                option_texts = request.form.getlist(f'new_option_{timestamp}[]')
                            
                            correct_index = ord(correct_letter) - ord('A') if correct_letter in 'ABCD' else 0
                            
                            print(f"DEBUG: Correct letter: {correct_letter}, index: {correct_index}, options: {option_texts}")
                            
                            # Insert options
                            for opt_idx, opt_text in enumerate(option_texts[:4]):  # Only take first 4
                                is_correct = 1 if opt_idx == correct_index else 0
                                if opt_text.strip():
                                    conn.execute(
                                        "INSERT INTO PracticeOptions (question_id, option_text, is_correct, option_order) VALUES (?, ?, ?, ?)",
                                        (question_id, opt_text, is_correct, opt_idx)
                                    )
                        except mysql.connector.IntegrityError as e:
                            print(f"DEBUG: IntegrityError while inserting question: {e}")
                            print(f"DEBUG: quiz_id={quiz_id}, question_id={question_id if 'question_id' in locals() else 'not set'}")
                            raise
            
            conn.commit()
            flash("Quiz updated successfully ✅", "success")
            # After saving edits, go back to the list of practice quizzes
            return redirect(url_for('list_practice_quizzes'))
        
        questions = conn.execute(
            "SELECT * FROM PracticeQuestions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchall()
        
        questions_with_options = []
        for q in questions:
            options = conn.execute(
                "SELECT * FROM PracticeOptions WHERE question_id=?",
                (q['question_id'],)
            ).fetchall()
            questions_with_options.append({
                "question": q,
                "options": options
            })
    
    return render_template(
        'teacher/edit_practice_quiz.html',
        quiz=quiz,
        questions=questions_with_options
    )


# ---------- ADD QUESTION TO PRACTICE QUIZ ----------
@app.route("/add_practice_question/<int:quiz_id>", methods=["POST"])
@login_required
def add_practice_question(quiz_id):
    if session.get('role') != 'Teacher':
        return redirect('/login')
    
    question_text = request.form.get('question_text')
    explanation = request.form.get('explanation', '')
    options = request.form.getlist('option_text[]')
    correct_index = int(request.form.get('correct_option', 0))
    
    with get_db_connection() as conn:
        # Verify quiz ownership
        quiz = conn.execute(
            "SELECT * FROM Practice_Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('list_practice_quizzes'))
        
        # Insert question
        cur = conn.execute(
            "INSERT INTO PracticeQuestions (quiz_id, question_text, explanation) VALUES (?, ?, ?)",
            (quiz_id, question_text, explanation)
        )
        question_id = cur.lastrowid
        
        # Insert options
        for i, opt in enumerate(options):
            is_correct = 1 if i == correct_index else 0
            conn.execute(
                "INSERT INTO PracticeOptions (question_id, option_text, is_correct, option_order) VALUES (?, ?, ?, ?)",
                (question_id, opt, is_correct, i)
            )
        
        conn.commit()
    
    flash("Question added successfully ✅", "success")
    return redirect(url_for('edit_practice_quiz', quiz_id=quiz_id))


# ---------- UPDATE PRACTICE QUESTION ----------
@app.route("/update_practice_question/<int:question_id>/<int:quiz_id>", methods=["POST"])
@login_required
def update_practice_question(question_id, quiz_id):
    if session.get('role') != 'Teacher':
        return redirect('/login')
    
    question_text = request.form.get('question_text')
    explanation = request.form.get('explanation', '')
    options = request.form.getlist('option_text[]')
    correct_index = int(request.form.get('correct_option', 0))
    
    with get_db_connection() as conn:
        # Verify quiz ownership
        quiz = conn.execute(
            "SELECT * FROM Practice_Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('list_practice_quizzes'))
        
        # Update question
        conn.execute(
            "UPDATE PracticeQuestions SET question_text=?, explanation=? WHERE question_id=?",
            (question_text, explanation, question_id)
        )
        
        # Update options
        existing_options = conn.execute(
            "SELECT option_id FROM PracticeOptions WHERE question_id=? ORDER BY option_order",
            (question_id,)
        ).fetchall()
        
        for i, opt_text in enumerate(options):
            is_correct = 1 if i == correct_index else 0
            if i < len(existing_options):
                conn.execute(
                    "UPDATE PracticeOptions SET option_text=?, is_correct=?, option_order=? WHERE option_id=?",
                    (opt_text, is_correct, i, existing_options[i]['option_id'])
                )
            else:
                conn.execute(
                    "INSERT INTO PracticeOptions (question_id, option_text, is_correct, option_order) VALUES (?, ?, ?, ?)",
                    (question_id, opt_text, is_correct, i)
                )
        
        conn.commit()
    
    flash("Question updated successfully ✅", "success")
    return redirect(url_for('edit_practice_quiz', quiz_id=quiz_id))


# ---------- DELETE PRACTICE QUESTION ----------
@app.route("/delete_practice_question/<int:question_id>/<int:quiz_id>", methods=["POST", "GET"])
@login_required
def delete_practice_question(question_id, quiz_id):
    if session.get('role') != 'Teacher':
        return redirect('/login')
    
    with get_db_connection() as conn:
        # Verify quiz ownership
        quiz = conn.execute(
            "SELECT * FROM Practice_Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('list_practice_quizzes'))
        
        # Delete options
        conn.execute("DELETE FROM PracticeOptions WHERE question_id=?", (question_id,))
        # Delete question
        conn.execute("DELETE FROM PracticeQuestions WHERE question_id=?", (question_id,))
        conn.commit()
    
    flash("Question deleted successfully ✅", "success")
    return redirect(url_for('edit_practice_quiz', quiz_id=quiz_id))


# ---------- DELETE PRACTICE QUIZ ----------
@app.route("/delete_practice_quiz/<int:quiz_id>", methods=["POST", "GET"])
@login_required
def delete_practice_quiz(quiz_id):
    if session.get('role') != 'Teacher':
        return redirect('/login')
    
    print(f"DEBUG: delete_practice_quiz called for quiz_id={quiz_id}, user_id={session.get('user_id')}, method={request.method}")
    
    try:
        with get_db_connection() as conn:
            # Verify quiz ownership
            quiz = conn.execute(
                "SELECT * FROM Practice_Quizzes WHERE quiz_id=? AND created_by=?",
                (quiz_id, session['user_id'])
            ).fetchone()
            
            if not quiz:
                print(f"DEBUG: Quiz {quiz_id} not found or not owned by user {session.get('user_id')}")
                flash("Quiz not found")
                return redirect(url_for('list_practice_quizzes'))
            
            print(f"DEBUG: Found quiz {quiz_id}, deleting related data...")
            
            # Temporarily disable foreign key constraints during multi-table delete
            conn.execute("PRAGMA foreign_keys = OFF")
            
            # 1️⃣ Delete options
            conn.execute("""
                DELETE FROM PracticeOptions
                WHERE question_id IN (
                    SELECT question_id FROM PracticeQuestions WHERE quiz_id=?
                )
            """, (quiz_id,))
            print(f"DEBUG: Deleted PracticeOptions")
            
            # 2️⃣ Delete questions
            conn.execute("DELETE FROM PracticeQuestions WHERE quiz_id=?", (quiz_id,))
            print(f"DEBUG: Deleted PracticeQuestions")
            
            # 3️⃣ Delete progress records
            conn.execute("DELETE FROM PracticeProgress WHERE quiz_id=?", (quiz_id,))
            print(f"DEBUG: Deleted PracticeProgress")
            
            # 4️⃣ Delete the quiz itself
            conn.execute("DELETE FROM Practice_Quizzes WHERE quiz_id=?", (quiz_id,))
            print(f"DEBUG: Deleted Practice_Quizzes")
            try:
                conn.execute("DELETE FROM PracticeQuizzes WHERE quiz_id=?", (quiz_id,))
            except Exception:
                pass
            
            # Re-enable foreign key constraints
            conn.execute("PRAGMA foreign_keys = ON")
            print(f"DEBUG: All deletions prepared for commit - quiz_id={quiz_id}")
        
        flash("Quiz deleted successfully ✅", "success")
    except Exception as e:
        print(f"ERROR: Delete practice quiz error: {type(e).__name__}: {e}")
        traceback.print_exc()
        flash("Error deleting quiz ❌", "danger")
    
    return redirect(url_for('teacher_dashboard'))
   

# Manage Practice Quiz
# -------------------------------
@app.route('/manage_practice_quiz')
@login_required
def manage_practice_quiz():

    with get_db_connection() as conn:
        quizzes = conn.execute("""
            SELECT * FROM Quizzes
            WHERE mode='practice' AND created_by=?
        """, (session['user_id'],)).fetchall()

    return render_template('manage_practice_quiz.html', quizzes=quizzes)



# ---------------- TEACHER DASHBOARD ----------------
@app.route('/teacher_dashboard')
@login_required
def teacher_dashboard():
    if session['role'] != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    with get_db_connection() as conn:

        # Regular Quizzes
        quizzes = conn.execute("""
            SELECT q.*, COUNT(ques.question_id) AS question_count
            FROM Quizzes q
            LEFT JOIN Questions ques ON q.quiz_id = ques.quiz_id
            WHERE q.created_by = ?
            GROUP BY q.quiz_id
            ORDER BY q.quiz_id DESC
        """, (session['user_id'],)).fetchall()

        # ✅ Practice Quizzes (FIXED)
        practice_quizzes = conn.execute("""
            SELECT p.*, COUNT(pq.question_id) AS question_count
            FROM Practice_Quizzes p
            LEFT JOIN PracticeQuestions pq ON p.quiz_id = pq.quiz_id
            WHERE p.created_by = ?
            GROUP BY p.quiz_id
            ORDER BY p.quiz_id DESC
        """, (session['user_id'],)).fetchall()

    return render_template(
        'teacher/dashboard.html',
        quizzes=quizzes,
        practice_quizzes=practice_quizzes
    )

@app.route('/teacher_live_quizzes')
@login_required
def teacher_live_quizzes():
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    with get_db_connection() as conn:
        quizzes = conn.execute("""
            SELECT q.*, COUNT(ques.question_id) AS question_count
            FROM Quizzes q
            LEFT JOIN Questions ques ON q.quiz_id = ques.quiz_id
            WHERE q.created_by = ?
            GROUP BY q.quiz_id
            ORDER BY q.quiz_id DESC
        """, (session['user_id'],)).fetchall()

    return render_template('teacher/live_quizzes.html', quizzes=quizzes)

@app.route('/teacher/practice_results')
@login_required
def teacher_practice_results_overview():
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    quiz_query = (request.args.get('q') or '').strip()

    with get_db_connection() as conn:
        filters = ["q.created_by=?"]
        params = [session['user_id']]
        if quiz_query:
            filters.append("LOWER(q.quiz_name) LIKE ?")
            params.append(f"%{quiz_query.lower()}%")

        quizzes = conn.execute(
            f"""
            SELECT
                q.quiz_id,
                q.quiz_name,
                q.created_at,
                COUNT(DISTINCT pfa.user_id) AS first_attempt_students
            FROM Practice_Quizzes q
            LEFT JOIN PracticeFirstAttempts pfa ON pfa.quiz_id = q.quiz_id
            WHERE {" AND ".join(filters)}
            GROUP BY q.quiz_id, q.quiz_name, q.created_at
            ORDER BY q.quiz_id DESC
            """,
            tuple(params)
        ).fetchall()

    return render_template(
        'teacher/practice_results_overview.html',
        quizzes=quizzes,
        quiz_query=quiz_query
    )

@app.route('/teacher/practice_results/<int:quiz_id>')
@login_required
def teacher_practice_quiz_results(quiz_id):
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    search_query = (request.args.get('q') or '').strip()
    selected_date = (request.args.get('date') or '').strip()

    with get_db_connection() as conn:
        quiz = conn.execute(
            "SELECT quiz_id, quiz_name FROM Practice_Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('teacher_practice_results_overview'))

        filters = ["pfa.quiz_id=?"]
        params = [quiz_id]
        if search_query:
            filters.append("LOWER(u.username) LIKE ?")
            params.append(f"%{search_query.lower()}%")
        if selected_date:
            filters.append("date(pfa.attempted_at)=?")
            params.append(selected_date)
        where_clause = " AND ".join(filters)

        first_attempts = conn.execute(
            f"""
            SELECT
                u.username AS student_name,
                COALESCE(NULLIF(u.department, ''), 'Unknown') AS branch,
                pfa.score,
                pfa.correct_answers,
                pfa.total_questions,
                pfa.attempted_at,
                date(pfa.attempted_at) AS attempt_date,
                pp.score AS latest_score,
                pp.correct_answers AS latest_correct,
                pp.total_questions AS latest_total,
                pp.completed_at AS latest_completed_at
            FROM PracticeFirstAttempts pfa
            JOIN Users u ON u.user_id = pfa.user_id
            LEFT JOIN PracticeProgress pp
                ON pp.user_id = pfa.user_id AND pp.quiz_id = pfa.quiz_id
            WHERE {where_clause}
            ORDER BY pfa.score DESC, pfa.correct_answers DESC, pfa.attempted_at ASC
            """,
            tuple(params)
        ).fetchall()

        summary = conn.execute(
            f"""
            SELECT
                date(pfa.attempted_at) AS attempt_date,
                COALESCE(NULLIF(u.department, ''), 'Unknown') AS branch,
                COUNT(*) AS students_count
            FROM PracticeFirstAttempts pfa
            JOIN Users u ON u.user_id = pfa.user_id
            WHERE {where_clause}
            GROUP BY date(pfa.attempted_at), COALESCE(NULLIF(u.department, ''), 'Unknown')
            ORDER BY attempt_date DESC, branch ASC
            """,
            tuple(params)
        ).fetchall()

        total_questions = conn.execute(
            "SELECT COUNT(*) AS total FROM PracticeQuestions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchone()["total"]

        question_stats = conn.execute(
            """
            SELECT
                q.question_id,
                q.question_text,
                COALESCE(SUM(CASE WHEN pa.is_correct=0 THEN 1 ELSE 0 END), 0) AS incorrect_count,
                COALESCE(SUM(CASE WHEN pa.is_correct=1 THEN 1 ELSE 0 END), 0) AS correct_count,
                COUNT(pa.answer_id) AS attempts
            FROM PracticeQuestions q
            LEFT JOIN PracticeAnswers pa
                ON pa.question_id = q.question_id
               AND pa.quiz_id = ?
            WHERE q.quiz_id = ?
            GROUP BY q.question_id, q.question_text
            ORDER BY incorrect_count DESC, attempts DESC
            """,
            (quiz_id, quiz_id)
        ).fetchall()

    attempted_students = len(first_attempts)
    class_avg_score = round(sum(r["score"] for r in first_attempts) / attempted_students, 2) if attempted_students else 0
    highest_score = max((r["score"] for r in first_attempts), default=0)
    lowest_score = min((r["score"] for r in first_attempts), default=0)
    top_performers = first_attempts[:5] if first_attempts else []

    total_correct = sum(r["correct_answers"] or 0 for r in first_attempts)
    total_attempted = sum(r["total_questions"] or 0 for r in first_attempts)
    total_incorrect = max(0, total_attempted - total_correct)

    difficulty_counts = {"easy": 0, "medium": 0, "difficult": 0, "no_data": 0}
    for q in question_stats:
        bucket = _difficulty_bucket(q["correct_count"], q["attempts"])
        difficulty_counts[bucket] += 1

    report = {
        "total_questions": total_questions,
        "attempted_students": attempted_students,
        "class_avg_score": class_avg_score,
        "highest_score": highest_score,
        "lowest_score": lowest_score,
        "top_performers": top_performers,
        "score_labels": [r["student_name"] for r in first_attempts],
        "score_values": [r["score"] for r in first_attempts],
        "correct_total": total_correct,
        "incorrect_total": total_incorrect,
        "difficulty_counts": difficulty_counts
    }

    return render_template(
        'teacher/practice_quiz_results_teacher.html',
        quiz=quiz,
        first_attempts=first_attempts,
        summary=summary,
        report=report,
        question_stats=question_stats,
        search_query=search_query,
        selected_date=selected_date
    )

@app.route('/teacher/practice_results/<int:quiz_id>/export')
@login_required
def teacher_practice_quiz_results_export(quiz_id):
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    with get_db_connection() as conn:
        quiz = conn.execute(
            "SELECT quiz_id, quiz_name, created_by, created_at FROM Practice_Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('teacher_practice_results_overview'))

        host_row = conn.execute(
            "SELECT username FROM Users WHERE user_id=?",
            (quiz["created_by"],)
        ).fetchone()
        players_count_row = conn.execute(
            "SELECT COUNT(DISTINCT user_id) AS players_count FROM PracticeFirstAttempts WHERE quiz_id=?",
            (quiz_id,)
        ).fetchone()

        final_rows = conn.execute(
            """
            SELECT
                u.username AS player_name,
                pfa.score AS score,
                pfa.correct_answers AS correct_answers,
                MAX(0, pfa.total_questions - pfa.correct_answers) AS incorrect_answers
            FROM PracticeFirstAttempts pfa
            JOIN Users u ON u.user_id = pfa.user_id
            WHERE pfa.quiz_id=?
            ORDER BY pfa.score DESC, pfa.correct_answers DESC, pfa.attempted_at ASC
            """,
            (quiz_id,)
        ).fetchall()

        question_rows = conn.execute(
            """
            SELECT question_id, question_text
            FROM PracticeQuestions
            WHERE quiz_id=?
            ORDER BY question_id ASC
            """,
            (quiz_id,)
        ).fetchall()

        option_rows = conn.execute(
            """
            SELECT
                po.question_id,
                po.option_text,
                po.is_correct
            FROM PracticeOptions po
            JOIN PracticeQuestions pq ON pq.question_id = po.question_id
            WHERE pq.quiz_id=?
            ORDER BY po.question_id ASC, COALESCE(po.option_order, po.option_id) ASC, po.option_id ASC
            """,
            (quiz_id,)
        ).fetchall()

        accuracy_rows = conn.execute(
            """
            SELECT
                pa.question_id,
                AVG(CASE WHEN pa.is_correct=1 THEN 1.0 ELSE 0.0 END) AS accuracy
            FROM PracticeAnswers pa
            WHERE pa.quiz_id=?
            GROUP BY pa.question_id
            """,
            (quiz_id,)
        ).fetchall()

        raw_rows = conn.execute(
            """
            SELECT
                pa.answer_id,
                pa.user_id AS session_id,
                u.username AS player_name,
                COALESCE(sel.option_text, '') AS answer,
                pa.question_id,
                pa.is_correct,
                CASE WHEN pa.is_correct=1 THEN 1 ELSE 0 END AS score_awarded,
                0 AS response_ms,
                pq.question_text,
                20 AS time_limit
            FROM PracticeAnswers pa
            JOIN Users u ON u.user_id = pa.user_id
            LEFT JOIN PracticeOptions sel ON sel.option_id = pa.selected_option_id
            LEFT JOIN PracticeQuestions pq ON pq.question_id = pa.question_id
            WHERE pa.quiz_id=?
            ORDER BY pa.user_id ASC, pa.answer_id ASC
            """,
            (quiz_id,)
        ).fetchall()

    option_map = {}
    correct_map = {}
    for row in option_rows:
        option_map.setdefault(row["question_id"], []).append(row["option_text"] or "")
        if int(_safe_float(row["is_correct"], 0)) == 1:
            correct_map.setdefault(row["question_id"], []).append(row["option_text"] or "")

    questions = []
    for q in question_rows:
        questions.append({
            "question_id": q["question_id"],
            "question_text": q["question_text"] or "",
            "time_limit": 20,
            "options": option_map.get(q["question_id"], []),
            "correct_answers": " | ".join(correct_map.get(q["question_id"], []))
        })

    accuracy_map = {r["question_id"]: _safe_float(r["accuracy"], 0.0) for r in accuracy_rows}
    played_on = str(quiz["created_at"]).split(" ")[0] if quiz["created_at"] else ""
    hosted_by = host_row["username"] if host_row else ""
    players_count = players_count_row["players_count"] if players_count_row else 0

    sheets = _build_kahoot_style_sheets(
        quiz_name=quiz["quiz_name"],
        played_on=played_on,
        hosted_by=hosted_by,
        players_count=players_count,
        final_rows=[dict(r) for r in final_rows],
        questions=questions,
        question_accuracy_map=accuracy_map,
        raw_rows=[dict(r) for r in raw_rows]
    )

    filename = f"practice_results_{quiz_id}.xlsx"
    return _xlsx_response(filename, sheets)

@app.route('/teacher/live_results')
@login_required
def teacher_live_results_overview():
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    quiz_query = (request.args.get('q') or '').strip()

    with get_db_connection() as conn:
        filters = ["q.created_by=?"]
        params = [session['user_id']]
        if quiz_query:
            filters.append("LOWER(q.quiz_name) LIKE ?")
            params.append(f"%{quiz_query.lower()}%")

        quizzes = conn.execute(
            f"""
            SELECT
                q.quiz_id,
                q.quiz_name,
                q.created_at,
                COUNT(DISTINCT ls.session_id) AS session_count
            FROM Quizzes q
            LEFT JOIN live_sessions ls ON ls.quiz_id = q.quiz_id
            WHERE {" AND ".join(filters)}
            GROUP BY q.quiz_id, q.quiz_name, q.created_at
            ORDER BY q.quiz_id DESC
            """,
            tuple(params)
        ).fetchall()

    return render_template(
        'teacher/live_results_overview.html',
        quizzes=quizzes,
        quiz_query=quiz_query
    )

@app.route('/teacher/live_results/<int:quiz_id>')
@login_required
def teacher_live_quiz_results(quiz_id):
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    search_query = (request.args.get('q') or '').strip()
    selected_date = (request.args.get('date') or '').strip()

    with get_db_connection() as conn:
        quiz = conn.execute(
            "SELECT quiz_id, quiz_name FROM Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('teacher_live_results_overview'))

        filters = []
        params = []
        if search_query:
            filters.append("LOWER(base.student_name) LIKE ?")
            params.append(f"%{search_query.lower()}%")
        if selected_date:
            filters.append("base.activity_date=?")
            params.append(selected_date)
        where_clause = " AND ".join(filters) if filters else "1=1"

        rows = conn.execute(
            f"""
            WITH base AS (
                SELECT
                    ls.quiz_id,
                    ls.session_id,
                    ls.pin,
                    p.nickname AS student_name,
                    COALESCE(NULLIF(u.department, ''), 'Unknown') AS branch,
                    date(COALESCE(MIN(pa.submitted_at), MIN(p.joined_at))) AS activity_date,
                    COUNT(pa.answer_id) AS answers_count,
                    COALESCE(SUM(pa.score_awarded), 0) AS score,
                    COALESCE(SUM(pa.is_correct), 0) AS correct_answers,
                    COALESCE(SUM(CASE WHEN pa.is_correct=1 THEN pa.response_ms ELSE 0 END), 0) AS time_taken
                FROM live_sessions ls
                JOIN participants p ON p.session_id = ls.session_id
                LEFT JOIN player_answers pa
                    ON pa.session_id = ls.session_id
                   AND pa.player_name = p.nickname
                LEFT JOIN Users u
                    ON LOWER(u.username) = LOWER(p.nickname)
                   AND u.role = 'Student'
                WHERE ls.quiz_id=?
                GROUP BY ls.quiz_id, ls.session_id, ls.pin, p.nickname, COALESCE(NULLIF(u.department, ''), 'Unknown')
            )
            SELECT
                base.session_id,
                base.pin,
                base.student_name,
                base.branch,
                base.activity_date,
                base.answers_count,
                base.score,
                base.correct_answers,
                base.time_taken
            FROM base
            WHERE {where_clause}
              AND base.answers_count > 0
            ORDER BY base.activity_date DESC, base.branch ASC, base.score DESC, base.correct_answers DESC, base.time_taken ASC, base.student_name ASC
            """,
            tuple([quiz_id] + params)
        ).fetchall()

        summary = conn.execute(
            f"""
            WITH base AS (
                SELECT
                    ls.quiz_id,
                    p.nickname AS student_name,
                    COALESCE(NULLIF(u.department, ''), 'Unknown') AS branch,
                    date(COALESCE(MIN(pa.submitted_at), MIN(p.joined_at))) AS activity_date,
                    COUNT(pa.answer_id) AS answers_count
                FROM live_sessions ls
                JOIN participants p ON p.session_id = ls.session_id
                LEFT JOIN player_answers pa
                    ON pa.session_id = ls.session_id
                   AND pa.player_name = p.nickname
                LEFT JOIN Users u
                    ON LOWER(u.username) = LOWER(p.nickname)
                   AND u.role = 'Student'
                WHERE ls.quiz_id=?
                GROUP BY ls.quiz_id, p.nickname, COALESCE(NULLIF(u.department, ''), 'Unknown')
            )
            SELECT
                base.activity_date,
                base.branch,
                COUNT(*) AS students_count
            FROM base
            WHERE {where_clause}
              AND base.answers_count > 0
            GROUP BY base.activity_date, base.branch
            ORDER BY base.activity_date DESC, base.branch ASC
            """,
            tuple([quiz_id] + params)
        ).fetchall()

        total_questions = conn.execute(
            "SELECT COUNT(*) AS total FROM Questions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchone()["total"]

        participants_total = conn.execute(
            """
            SELECT COUNT(DISTINCT p.nickname) AS total
            FROM participants p
            JOIN live_sessions ls ON ls.session_id = p.session_id
            WHERE ls.quiz_id=?
            """,
            (quiz_id,)
        ).fetchone()["total"]

        question_stats = conn.execute(
            """
            WITH sessions AS (
                SELECT session_id FROM live_sessions WHERE quiz_id=?
            )
            SELECT
                q.question_id,
                q.question_text,
                COALESCE(SUM(CASE WHEN pa.is_correct=0 THEN 1 ELSE 0 END), 0) AS incorrect_count,
                COALESCE(SUM(CASE WHEN pa.is_correct=1 THEN 1 ELSE 0 END), 0) AS correct_count,
                COUNT(pa.answer_id) AS attempts
            FROM Questions q
            LEFT JOIN player_answers pa
                ON pa.question_id = q.question_id
               AND pa.session_id IN (SELECT session_id FROM sessions)
            WHERE q.quiz_id = ?
            GROUP BY q.question_id, q.question_text
            ORDER BY incorrect_count DESC, attempts DESC
            """,
            (quiz_id, quiz_id)
        ).fetchall()

    attempted_students = len(rows)
    class_avg_score = round(sum(r["score"] for r in rows) / attempted_students, 2) if attempted_students else 0
    highest_score = max((r["score"] for r in rows), default=0)
    lowest_score = min((r["score"] for r in rows), default=0)
    top_performers = rows[:5] if rows else []

    total_correct = sum(r["correct_answers"] or 0 for r in rows)
    total_attempted = sum(r["answers_count"] or 0 for r in rows)
    total_incorrect = max(0, total_attempted - total_correct)

    difficulty_counts = {"easy": 0, "medium": 0, "difficult": 0, "no_data": 0}
    for q in question_stats:
        bucket = _difficulty_bucket(q["correct_count"], q["attempts"])
        difficulty_counts[bucket] += 1

    date_buckets = {}
    for r in rows:
        key = r["activity_date"]
        if key not in date_buckets:
            date_buckets[key] = []
        date_buckets[key].append(r["score"] or 0)
    date_labels = sorted(date_buckets.keys()) if date_buckets else []
    date_avg_scores = [
        round(sum(date_buckets[d]) / len(date_buckets[d]), 2) for d in date_labels
    ]

    report = {
        "total_questions": total_questions,
        "participants_total": participants_total,
        "attempted_students": attempted_students,
        "incomplete_students": max(0, participants_total - attempted_students),
        "class_avg_score": class_avg_score,
        "highest_score": highest_score,
        "lowest_score": lowest_score,
        "top_performers": top_performers,
        "score_labels": [r["student_name"] for r in rows],
        "score_values": [r["score"] for r in rows],
        "correct_total": total_correct,
        "incorrect_total": total_incorrect,
        "difficulty_counts": difficulty_counts,
        "date_labels": date_labels,
        "date_avg_scores": date_avg_scores
    }

    return render_template(
        'teacher/live_quiz_results_teacher.html',
        quiz=quiz,
        rows=rows,
        summary=summary,
        report=report,
        question_stats=question_stats,
        search_query=search_query,
        selected_date=selected_date
    )

@app.route('/teacher/live_results/<int:quiz_id>/export')
@login_required
def teacher_live_quiz_results_export(quiz_id):
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    with get_db_connection() as conn:
        quiz = conn.execute(
            "SELECT quiz_id, quiz_name, created_at, created_by FROM Quizzes WHERE quiz_id=? AND created_by=?",
            (quiz_id, session['user_id'])
        ).fetchone()
        if not quiz:
            flash("Quiz not found")
            return redirect(url_for('teacher_live_results_overview'))

        host_row = conn.execute(
            "SELECT username FROM Users WHERE user_id=?",
            (quiz["created_by"],)
        ).fetchone()
        played_on_row = conn.execute(
            "SELECT COALESCE(date(MIN(start_time)), date(?)) AS played_on FROM live_sessions WHERE quiz_id=?",
            (quiz["created_at"], quiz_id)
        ).fetchone()
        players_count_row = conn.execute(
            """
            SELECT COUNT(DISTINCT p.nickname) AS players_count
            FROM live_sessions ls
            JOIN participants p ON p.session_id = ls.session_id
            WHERE ls.quiz_id=?
            """,
            (quiz_id,)
        ).fetchone()

        final_rows = conn.execute(
            """
            WITH per_player AS (
                SELECT
                    p.nickname AS player_name,
                    COUNT(pa.answer_id) AS attempted_answers,
                    COALESCE(SUM(pa.is_correct), 0) AS correct_answers,
                    COALESCE(SUM(pa.score_awarded), 0) AS score
                FROM live_sessions ls
                JOIN participants p ON p.session_id = ls.session_id
                LEFT JOIN player_answers pa
                    ON pa.session_id = ls.session_id
                   AND pa.player_name = p.nickname
                WHERE ls.quiz_id=?
                GROUP BY p.nickname
            )
            SELECT
                player_name,
                score,
                correct_answers,
                MAX(0, attempted_answers - correct_answers) AS incorrect_answers
            FROM per_player
            WHERE attempted_answers > 0
            ORDER BY score DESC, correct_answers DESC, player_name ASC
            """,
            (quiz_id,)
        ).fetchall()

        question_rows = conn.execute(
            """
            SELECT question_id, question_text, COALESCE(time_limit, 20) AS time_limit
            FROM questions
            WHERE quiz_id=?
            ORDER BY question_id ASC
            """,
            (quiz_id,)
        ).fetchall()

        option_rows = conn.execute(
            """
            SELECT
                o.question_id,
                o.option_text,
                o.is_correct
            FROM options o
            JOIN questions q ON q.question_id = o.question_id
            WHERE q.quiz_id=?
            ORDER BY o.question_id ASC, COALESCE(o.option_order, o.option_id) ASC, o.option_id ASC
            """,
            (quiz_id,)
        ).fetchall()

        accuracy_rows = conn.execute(
            """
            SELECT
                pa.question_id,
                AVG(CASE WHEN pa.is_correct=1 THEN 1.0 ELSE 0.0 END) AS accuracy
            FROM player_answers pa
            JOIN live_sessions ls ON ls.session_id = pa.session_id
            WHERE ls.quiz_id=?
            GROUP BY pa.question_id
            """,
            (quiz_id,)
        ).fetchall()

        raw_rows = conn.execute(
            """
            SELECT
                pa.answer_id,
                pa.session_id,
                pa.player_name,
                pa.answer,
                pa.question_id,
                pa.is_correct,
                pa.score_awarded,
                pa.response_ms,
                q.question_text,
                COALESCE(q.time_limit, 20) AS time_limit
            FROM player_answers pa
            JOIN live_sessions ls ON ls.session_id = pa.session_id
            LEFT JOIN questions q ON q.question_id = pa.question_id
            WHERE ls.quiz_id=?
            ORDER BY pa.session_id ASC, pa.player_name ASC, pa.answer_id ASC
            """,
            (quiz_id,)
        ).fetchall()

    option_map = {}
    correct_map = {}
    for row in option_rows:
        option_map.setdefault(row["question_id"], []).append(row["option_text"] or "")
        if int(_safe_float(row["is_correct"], 0)) == 1:
            correct_map.setdefault(row["question_id"], []).append(row["option_text"] or "")

    questions = []
    for q in question_rows:
        questions.append({
            "question_id": q["question_id"],
            "question_text": q["question_text"] or "",
            "time_limit": q["time_limit"] or 20,
            "options": option_map.get(q["question_id"], []),
            "correct_answers": " | ".join(correct_map.get(q["question_id"], []))
        })

    accuracy_map = {r["question_id"]: _safe_float(r["accuracy"], 0.0) for r in accuracy_rows}
    played_on = played_on_row["played_on"] if played_on_row and played_on_row["played_on"] else ""
    hosted_by = host_row["username"] if host_row else ""
    players_count = players_count_row["players_count"] if players_count_row else 0

    sheets = _build_kahoot_style_sheets(
        quiz_name=quiz["quiz_name"],
        played_on=played_on,
        hosted_by=hosted_by,
        players_count=players_count,
        final_rows=[dict(r) for r in final_rows],
        questions=questions,
        question_accuracy_map=accuracy_map,
        raw_rows=[dict(r) for r in raw_rows]
    )

    filename = f"live_results_{quiz_id}.xlsx"
    return _xlsx_response(filename, sheets)

@app.route('/teacher/reports')
@login_required
def teacher_reports():
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    with get_db_connection() as conn:
        live_rows = conn.execute(
            """
            WITH base AS (
                SELECT
                    p.nickname AS student_name,
                    COUNT(DISTINCT ls.session_id) AS sessions_attempted,
                    COUNT(pa.answer_id) AS answers_count,
                    COALESCE(SUM(pa.score_awarded), 0) AS total_score,
                    COALESCE(SUM(pa.is_correct), 0) AS correct_answers
                FROM live_sessions ls
                JOIN participants p ON p.session_id = ls.session_id
                LEFT JOIN player_answers pa
                    ON pa.session_id = ls.session_id
                   AND pa.player_name = p.nickname
                WHERE ls.quiz_id IN (
                    SELECT quiz_id FROM Quizzes WHERE created_by=?
                )
                GROUP BY p.nickname
            )
            SELECT * FROM base
            WHERE answers_count > 0
            ORDER BY total_score DESC, correct_answers DESC, student_name ASC
            """,
            (session['user_id'],)
        ).fetchall()

        practice_rows = conn.execute(
            """
            SELECT
                u.username AS student_name,
                COUNT(*) AS attempts,
                AVG(pfa.score) AS avg_score,
                SUM(pfa.correct_answers) AS correct_answers,
                SUM(pfa.total_questions) AS total_questions
            FROM PracticeFirstAttempts pfa
            JOIN Practice_Quizzes q ON q.quiz_id = pfa.quiz_id
            JOIN Users u ON u.user_id = pfa.user_id
            WHERE q.created_by = ?
            GROUP BY u.username
            ORDER BY avg_score DESC, student_name ASC
            """,
            (session['user_id'],)
        ).fetchall()

    live_map = {}
    for r in live_rows:
        key = (r["student_name"] or "").strip().lower()
        live_map[key] = {
            "student_name": r["student_name"],
            "sessions_attempted": r["sessions_attempted"],
            "live_total_score": r["total_score"],
            "live_avg_score": round((r["total_score"] / r["sessions_attempted"]), 2) if r["sessions_attempted"] else 0,
            "live_correct": r["correct_answers"],
            "live_answers": r["answers_count"]
        }

    practice_map = {}
    for r in practice_rows:
        key = (r["student_name"] or "").strip().lower()
        practice_map[key] = {
            "student_name": r["student_name"],
            "practice_attempts": r["attempts"],
            "practice_avg_score": round(r["avg_score"], 2) if r["avg_score"] is not None else 0,
            "practice_correct": r["correct_answers"],
            "practice_total": r["total_questions"]
        }

    all_keys = sorted(set(live_map.keys()) | set(practice_map.keys()))
    rows = []
    for key in all_keys:
        live = live_map.get(key, {})
        practice = practice_map.get(key, {})
        student_name = live.get("student_name") or practice.get("student_name") or key
        live_avg = live.get("live_avg_score", 0)
        practice_avg = practice.get("practice_avg_score", 0)
        divisor = (1 if live_avg else 0) + (1 if practice_avg else 0)
        combined = round((live_avg + practice_avg) / divisor, 2) if divisor else 0
        rows.append({
            "student_name": student_name,
            "live_avg_score": live_avg,
            "live_sessions": live.get("sessions_attempted", 0),
            "practice_avg_score": practice_avg,
            "practice_attempts": practice.get("practice_attempts", 0),
            "combined_score": combined
        })

    rows.sort(key=lambda r: (-(r["combined_score"] or 0), r["student_name"]))

    avg_live = round(
        sum(r["live_avg_score"] for r in rows if r["live_avg_score"]) / max(1, len([r for r in rows if r["live_avg_score"]])),
        2
    ) if rows else 0
    avg_practice = round(
        sum(r["practice_avg_score"] for r in rows if r["practice_avg_score"]) / max(1, len([r for r in rows if r["practice_avg_score"]])),
        2
    ) if rows else 0

    summary = {
        "total_students": len(rows),
        "avg_live_score": avg_live,
        "avg_practice_score": avg_practice,
        "top_performers": rows[:5]
    }

    return render_template(
        'teacher/reports.html',
        rows=rows,
        summary=summary
    )

@app.route('/teacher/reports/export')
@login_required
def teacher_reports_export():
    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    with get_db_connection() as conn:
        live_rows = conn.execute(
            """
            WITH base AS (
                SELECT
                    p.nickname AS student_name,
                    COUNT(DISTINCT ls.session_id) AS sessions_attempted,
                    COUNT(pa.answer_id) AS answers_count,
                    COALESCE(SUM(pa.score_awarded), 0) AS total_score
                FROM live_sessions ls
                JOIN participants p ON p.session_id = ls.session_id
                LEFT JOIN player_answers pa
                    ON pa.session_id = ls.session_id
                   AND pa.player_name = p.nickname
                WHERE ls.quiz_id IN (
                    SELECT quiz_id FROM Quizzes WHERE created_by=?
                )
                GROUP BY p.nickname
            )
            SELECT * FROM base
            WHERE answers_count > 0
            """,
            (session['user_id'],)
        ).fetchall()

        practice_rows = conn.execute(
            """
            SELECT
                u.username AS student_name,
                COUNT(*) AS attempts,
                AVG(pfa.score) AS avg_score
            FROM PracticeFirstAttempts pfa
            JOIN Practice_Quizzes q ON q.quiz_id = pfa.quiz_id
            JOIN Users u ON u.user_id = pfa.user_id
            WHERE q.created_by = ?
            GROUP BY u.username
            """,
            (session['user_id'],)
        ).fetchall()

    live_map = {(r["student_name"] or "").strip().lower(): r for r in live_rows}
    practice_map = {(r["student_name"] or "").strip().lower(): r for r in practice_rows}
    all_keys = sorted(set(live_map.keys()) | set(practice_map.keys()))

    headers = [
        "Student",
        "Live Avg Score",
        "Live Sessions",
        "Practice Avg Score",
        "Practice Attempts",
        "Combined Score"
    ]
    data = []
    for key in all_keys:
        live = live_map.get(key)
        practice = practice_map.get(key)
        student_name = (live["student_name"] if live else None) or (practice["student_name"] if practice else key)
        live_avg = round((live["total_score"] / live["sessions_attempted"]), 2) if live and live["sessions_attempted"] else 0
        practice_avg = round(practice["avg_score"], 2) if practice and practice["avg_score"] is not None else 0
        divisor = (1 if live_avg else 0) + (1 if practice_avg else 0)
        combined = round((live_avg + practice_avg) / divisor, 2) if divisor else 0
        data.append([
            student_name,
            live_avg,
            live["sessions_attempted"] if live else 0,
            practice_avg,
            practice["attempts"] if practice else 0,
            combined
        ])

    filename = "teacher_reports.csv"
    return _csv_response(filename, headers, data)


@app.route('/create_quiz/<quiz_type>', methods=['GET', 'POST'])
@login_required
def create_quiz(quiz_type):

    if session.get('role') != 'Teacher':
        flash("Access denied")
        return redirect('/login')

    if request.method == 'POST':

        title = request.form['title']
        description = request.form.get('description', '')
        try:
            time_per_question = int(request.form.get('time_per_question', 20))
        except ValueError:
            time_per_question = 20
        time_per_question = max(5, min(time_per_question, 300))
        teacher_id = session['user_id']

        try:
            with get_db_connection() as conn:

                # 🔥 INSERT BASED ON TYPE
                if quiz_type == "live":

                    cursor = conn.execute("""
                        INSERT INTO Quizzes (quiz_name, description, created_by)
                        VALUES (?, ?, ?)
                    """, (title, description, teacher_id))

                elif quiz_type == "practice":
                    selected_departments = normalize_departments(request.form.getlist('departments'))
                    if not selected_departments:
                        flash("Please select at least one department")
                        return redirect(url_for('create_quiz', quiz_type='practice'))

                    cursor = conn.execute("""
                        INSERT INTO Practice_Quizzes (quiz_name, description, teacher_id, created_by, target_departments)
                        VALUES (?, ?, ?, ?, ?)
                    """, (title, description, teacher_id, teacher_id, ",".join(selected_departments)))

                else:
                    flash("Invalid quiz type")
                    return redirect('/teacher_dashboard')

                quiz_id = cursor.lastrowid
                if quiz_type == "practice":
                    ensure_legacy_practice_quiz_row(conn, quiz_id, title, description)

                # ---------------- Questions ----------------
                questions = request.form.getlist('question[]')
                question_time_limits = request.form.getlist('question_time_limit[]')
                option_a_list = request.form.getlist('option_a[]')
                option_b_list = request.form.getlist('option_b[]')
                option_c_list = request.form.getlist('option_c[]')
                option_d_list = request.form.getlist('option_d[]')

                correct_options_dict = {}
                for key in request.form.keys():
                    if key.startswith("correct_option"):
                        idx = key[key.find("[")+1:key.find("]")]
                        correct_options_dict[idx] = request.form[key]

                for i, q_text in enumerate(questions):
                    per_question_time = time_per_question
                    if quiz_type == "live":
                        try:
                            per_question_time = int(question_time_limits[i])
                        except (ValueError, IndexError):
                            per_question_time = 20
                        per_question_time = max(5, min(per_question_time, 300))

                    q_cursor = conn.execute("""
                        INSERT INTO Questions 
                        (quiz_id, question_text, question_type, time_limit)
                        VALUES (?, ?, ?, ?)
                    """, (quiz_id, q_text, "Multiple Choice", per_question_time))

                    question_id = q_cursor.lastrowid

                    correct_code = correct_options_dict.get(str(i))

                    options = [
                        ('A', option_a_list[i]),
                        ('B', option_b_list[i]),
                        ('C', option_c_list[i]),
                        ('D', option_d_list[i])
                    ]

                    for code, text in options:
                        is_correct = 1 if code == correct_code else 0
                        conn.execute("""
                            INSERT INTO Options 
                            (question_id, option_text, is_correct)
                            VALUES (?, ?, ?)
                        """, (question_id, text, is_correct))

                conn.commit()

            flash(f"{quiz_type.capitalize()} quiz created successfully!")
            return redirect('/teacher_dashboard')

        except Exception as e:
            print("Error:", e)
            flash("Error creating quiz. Check console.")
            return redirect(request.url)

    return render_template('teacher/create_quiz.html', quiz_type=quiz_type)

@app.route('/start_quiz/<int:quiz_id>')
def start_quiz(quiz_id):
    if 'role' not in session or session['role'] != 'Teacher':
        flash("Please login as teacher")
        return redirect('/login')

    conn = get_db_connection()
    pin = random.randint(100000, 999999)  # 6-digit PIN

    # Insert live session
    conn.execute("""
        INSERT INTO live_sessions (quiz_id, pin, created_by)
        VALUES (?, ?, ?)
    """, (quiz_id, pin, session['user_id']))
    conn.commit()

    # Get the session_id
    session_id = conn.execute("SELECT last_insert_rowid() AS id").fetchone()['id']
    conn.close()

    return redirect(f'/host_lobby/{session_id}')

# ---------------- DELETE QUESTION ----------------

@app.route('/delete_question/<int:question_id>/<int:quiz_id>')
@login_required
def delete_question(question_id, quiz_id):

    if session.get('role') != 'Teacher':
        return redirect('/login')

    with get_db_connection() as conn:
        conn.execute("DELETE FROM Options WHERE question_id=?", (question_id,))
        conn.execute("DELETE FROM Questions WHERE question_id=?", (question_id,))
        conn.commit()

    flash("Question deleted")
    return redirect(f'/edit_quiz/{quiz_id}')


@app.route('/add_question/<int:quiz_id>', methods=['POST'])
@login_required
def add_question(quiz_id):

    question_text = request.form['question_text']
    options = request.form.getlist('option_text[]')
    correct_index = int(request.form['correct_option'])

    with get_db_connection() as conn:

        # Insert question
        cur = conn.execute(
            "INSERT INTO Questions (quiz_id, question_text) VALUES (?, ?)",
            (quiz_id, question_text)
        )
        question_id = cur.lastrowid

        # Insert options
        for i, opt in enumerate(options):
            is_correct = 1 if i == correct_index else 0
            conn.execute(
                "INSERT INTO Options (question_id, option_text, is_correct) VALUES (?, ?, ?)",
                (question_id, opt, is_correct)
            )

        conn.commit()

    flash("Question added successfully")
    return redirect(url_for('edit_quiz', quiz_id=quiz_id))

# ---------------- EDIT QUIZ ----------------
@app.route('/edit_quiz/<int:quiz_id>', methods=['GET'])
@login_required
def edit_quiz(quiz_id):
    if session.get('role') != 'Teacher':
        return redirect('/login')

    with get_db_connection() as conn:
        quiz = conn.execute(
            "SELECT * FROM Quizzes WHERE quiz_id=?",
            (quiz_id,)
        ).fetchone()

        questions = conn.execute(
            "SELECT * FROM Questions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchall()

        questions_with_options = []
        for q in questions:
            options = conn.execute(
                "SELECT * FROM Options WHERE question_id=?",
                (q['question_id'],)
            ).fetchall()

            questions_with_options.append({
                "question": q,
                "options": options
            })

    return render_template(
        'teacher/edit_quiz.html',
        quiz=quiz,
        questions=questions_with_options
    )

@app.route('/delete_quiz/<int:quiz_id>', methods=['POST'])
@login_required
def delete_quiz(quiz_id):

    if session.get('role') != 'Teacher':
        return redirect('/login')

    try:
        with get_db_connection() as conn:

            # 1️⃣ Delete Options
            conn.execute("""
                DELETE FROM Options
                WHERE question_id IN (
                    SELECT question_id FROM Questions WHERE quiz_id=?
                )
            """, (quiz_id,))

            # 2️⃣ Delete Questions
            conn.execute("DELETE FROM Questions WHERE quiz_id=?", (quiz_id,))

            # 3️⃣ Delete participants
            conn.execute("""
                DELETE FROM participants
                WHERE session_id IN (
                    SELECT session_id FROM live_sessions WHERE quiz_id=?
                )
            """, (quiz_id,))

            # 4️⃣ Delete live sessions
            conn.execute("DELETE FROM live_sessions WHERE quiz_id=?", (quiz_id,))

            # 5️⃣ Delete PlayerScores
            conn.execute("""
                DELETE FROM PlayerScores
                WHERE session_id IN (
                    SELECT session_id FROM GameSessions WHERE quiz_id=?
                )
            """, (quiz_id,))

            # 6️⃣ Delete GameSessions
            conn.execute("DELETE FROM GameSessions WHERE quiz_id=?", (quiz_id,))

            # 7️⃣ Finally delete Quiz
            conn.execute("DELETE FROM Quizzes WHERE quiz_id=?", (quiz_id,))

            conn.commit()

        flash("Quiz deleted successfully ✅", "success")

    except Exception as e:
        print("Delete quiz error:", e)
        flash("Error deleting quiz ❌", "danger")

    return redirect(url_for('teacher_dashboard'))



# ---------------- UPDATE QUIZ ----------------
@app.route('/update_quiz/<int:quiz_id>', methods=['POST'])
@login_required
def update_quiz(quiz_id):

    if session.get('role') != 'Teacher':
        return redirect('/login')

    conn = get_db_connection()
    cur = conn.cursor()

    # -------- UPDATE EXISTING QUESTIONS --------
    question_ids = request.form.getlist('question_id[]')
    question_texts = request.form.getlist('question_text[]')

    option_ids = request.form.getlist('option_id[]')
    option_texts = request.form.getlist('option_text[]')

    opt_index = 0

    for qid, qtext in zip(question_ids, question_texts):

        cur.execute(
            "UPDATE Questions SET question_text=? WHERE question_id=?",
            (qtext, qid)
        )

        correct_option_id = request.form.get(f'correct_{qid}')

        for _ in range(4):
            oid = option_ids[opt_index]
            otext = option_texts[opt_index]

            is_correct = 1 if str(oid) == str(correct_option_id) else 0

            cur.execute(
                "UPDATE Options SET option_text=?, is_correct=? WHERE option_id=?",
                (otext, is_correct, oid)
            )

            opt_index += 1

    # -------- ADD NEW QUESTIONS --------
    new_questions = request.form.getlist('new_question[]')

    if new_questions:
        new_q_texts = request.form.getlist('question_text[]')[-len(new_questions):]

        option1 = request.form.getlist('option1[]')
        option2 = request.form.getlist('option2[]')
        option3 = request.form.getlist('option3[]')
        option4 = request.form.getlist('option4[]')

        for i, qtext in enumerate(new_q_texts):
            cur.execute(
                "INSERT INTO Questions (quiz_id, question_text) VALUES (?, ?)",
                (quiz_id, qtext)
            )

            new_qid = cur.lastrowid
            correct = request.form.get(f'correct_{i}')

            options = [
                (option1[i], 'A'),
                (option2[i], 'B'),
                (option3[i], 'C'),
                (option4[i], 'D')
            ]

            for opt_text, label in options:
                is_correct = 1 if correct == label else 0
                cur.execute(
                    "INSERT INTO Options (question_id, option_text, is_correct) VALUES (?,?,?)",
                    (new_qid, opt_text, is_correct)
                )

    conn.commit()
    conn.close()

    # ✅ SUCCESS MESSAGE + DASHBOARD REDIRECT
    flash("Quiz updated successfully!", "success")
    return redirect(url_for('teacher_dashboard'))




@app.route('/leaderboard/<int:session_id>')
def leaderboard(session_id):
    with get_db_connection() as conn:
        scores = conn.execute("""
            SELECT user_id, score, correct_answers FROM PlayerScores
            WHERE session_id=?
            ORDER BY score DESC
        """, (session_id,)).fetchall()
    return render_template('shared/leaderboard.html', scores=scores)


@app.route('/student_practice_quizzes')
@login_required
def student_practice_quizzes():
    if session.get('role') != 'Student':
        return redirect('/login')

    with get_db_connection() as conn:
        student_department_row = conn.execute(
            "SELECT COALESCE(NULLIF(department, ''), 'Computer') AS department FROM Users WHERE user_id=?",
            (session['user_id'],)
        ).fetchone()
        student_department = student_department_row['department'] if student_department_row else 'Computer'

        quizzes = conn.execute("""
            SELECT
                p.quiz_id,
                p.quiz_name,
                p.description,
                p.created_at,
                COALESCE(u.username, 'Teacher') AS teacher_name,
                COALESCE(
                    NULLIF(p.target_departments, ''),
                    COALESCE(NULLIF(p.department, ''), COALESCE(NULLIF(u.department, ''), 'Computer'))
                ) AS quiz_departments,
                COUNT(DISTINCT q.question_id) AS total_questions,
                pp.score AS last_score,
                pp.correct_answers AS last_correct,
                pp.total_questions AS last_total,
                pp.completed_at
            FROM Practice_Quizzes p
            LEFT JOIN Users u ON p.created_by = u.user_id
            LEFT JOIN PracticeQuestions q ON p.quiz_id = q.quiz_id
            LEFT JOIN PracticeProgress pp
                ON pp.quiz_id = p.quiz_id AND pp.user_id = ?
            WHERE (',' || COALESCE(
                NULLIF(p.target_departments, ''),
                COALESCE(NULLIF(p.department, ''), COALESCE(NULLIF(u.department, ''), 'Computer'))
            ) || ',') LIKE '%,' || ? || ',%'
            GROUP BY p.quiz_id
            ORDER BY p.quiz_id DESC
        """, (session['user_id'], student_department)).fetchall()

    return render_template(
        'student/student_practice_quizzes.html',
        quizzes=quizzes,
        student_department=student_department
    )


@app.route('/take_practice_quiz/<int:quiz_id>')
@login_required
def take_practice_quiz(quiz_id):
    if session.get('role') != 'Student':
        return redirect('/login')

    with get_db_connection() as conn:
        student_department_row = conn.execute(
            "SELECT COALESCE(NULLIF(department, ''), 'Computer') AS department FROM Users WHERE user_id=?",
            (session['user_id'],)
        ).fetchone()
        student_department = student_department_row['department'] if student_department_row else 'Computer'

        quiz = conn.execute(
            """
            SELECT p.*
            FROM Practice_Quizzes p
            LEFT JOIN Users u ON p.created_by = u.user_id
            WHERE p.quiz_id=?
              AND (',' || COALESCE(
                    NULLIF(p.target_departments, ''),
                    COALESCE(NULLIF(p.department, ''), COALESCE(NULLIF(u.department, ''), 'Computer'))
                  ) || ',') LIKE '%,' || ? || ',%'
            """,
            (quiz_id, student_department)
        ).fetchone()
        if not quiz:
            flash("This quiz is not available for your department")
            return redirect(url_for('student_practice_quizzes'))

        questions = conn.execute(
            "SELECT * FROM PracticeQuestions WHERE quiz_id=? ORDER BY question_id",
            (quiz_id,)
        ).fetchall()

        questions_with_options = []
        for q in questions:
            options = conn.execute(
                "SELECT * FROM PracticeOptions WHERE question_id=? ORDER BY option_order, option_id",
                (q['question_id'],)
            ).fetchall()
            questions_with_options.append({
                "question": q,
                "options": options
            })

    return render_template(
        'student/take_practice_quiz.html',
        quiz=quiz,
        questions=questions_with_options
    )


@app.route('/download_practice_quiz/<int:quiz_id>')
@login_required
def download_practice_quiz(quiz_id):
    if session.get('role') != 'Student':
        return redirect('/login')

    user_id = session['user_id']

    with get_db_connection() as conn:
        student_department_row = conn.execute(
            "SELECT COALESCE(NULLIF(department, ''), 'Computer') AS department FROM Users WHERE user_id=?",
            (user_id,)
        ).fetchone()
        student_department = student_department_row['department'] if student_department_row else 'Computer'

        quiz = conn.execute(
            """
            SELECT p.*
            FROM Practice_Quizzes p
            LEFT JOIN Users u ON p.created_by = u.user_id
            WHERE p.quiz_id=?
              AND (',' || COALESCE(
                    NULLIF(p.target_departments, ''),
                    COALESCE(NULLIF(p.department, ''), COALESCE(NULLIF(u.department, ''), 'Computer'))
                  ) || ',') LIKE '%,' || ? || ',%'
            """,
            (quiz_id, student_department)
        ).fetchone()
        if not quiz:
            flash("This quiz is not available for your department")
            return redirect(url_for('student_practice_quizzes'))

        questions = conn.execute(
            "SELECT question_id, question_text, explanation FROM PracticeQuestions WHERE quiz_id=? ORDER BY question_id",
            (quiz_id,)
        ).fetchall()

        if not questions:
            flash("No questions found in this quiz")
            return redirect(url_for('student_practice_quizzes'))

        progress = conn.execute(
            """
            SELECT completed_at
            FROM PracticeProgress
            WHERE user_id=? AND quiz_id=?
            """,
            (user_id, quiz_id)
        ).fetchone()
        if not progress or not progress['completed_at']:
            flash("Please solve and submit the quiz first, then download answers.")
            return redirect(url_for('take_practice_quiz', quiz_id=quiz_id))

        lines = [
            f"Quiz: {quiz['quiz_name']}",
            f"Description: {quiz['description'] or ''}",
            f"Downloaded By User ID: {user_id}",
            f"Downloaded At: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            ""
        ]

        for idx, q in enumerate(questions, start=1):
            options = conn.execute(
                "SELECT option_id, option_text, is_correct FROM PracticeOptions WHERE question_id=? ORDER BY option_order, option_id",
                (q['question_id'],)
            ).fetchall()
            correct_text = ""
            for opt in options:
                if opt['is_correct'] == 1:
                    correct_text = opt['option_text']
                    break
            lines.append(f"Q{idx}. {q['question_text']}")
            for opt_idx, opt in enumerate(options):
                label = chr(ord('A') + opt_idx)
                lines.append(f"   {label}. {opt['option_text']}")
            lines.append(f"Correct Answer: {correct_text or 'N/A'}")
            if q['explanation']:
                lines.append(f"Explanation: {q['explanation']}")
            lines.append("")

    content = "\n".join(lines)
    filename = f"{slugify_filename(quiz['quiz_name'])}_with_answers.txt"
    return Response(
        content,
        mimetype='text/plain; charset=utf-8',
        headers={"Content-Disposition": f'attachment; filename="{filename}"'}
    )


@app.route('/download_practice_quiz_page/<int:quiz_id>')
@login_required
def download_practice_quiz_page(quiz_id):
    if session.get('role') != 'Student':
        return redirect('/login')

    user_id = session['user_id']
    with get_db_connection() as conn:
        student_department_row = conn.execute(
            "SELECT COALESCE(NULLIF(department, ''), 'Computer') AS department FROM Users WHERE user_id=?",
            (user_id,)
        ).fetchone()
        student_department = student_department_row['department'] if student_department_row else 'Computer'

        quiz = conn.execute(
            """
            SELECT p.quiz_id, p.quiz_name, p.description
            FROM Practice_Quizzes p
            LEFT JOIN Users u ON p.created_by = u.user_id
            WHERE p.quiz_id=?
              AND (',' || COALESCE(
                    NULLIF(p.target_departments, ''),
                    COALESCE(NULLIF(p.department, ''), COALESCE(NULLIF(u.department, ''), 'Computer'))
                  ) || ',') LIKE '%,' || ? || ',%'
            """,
            (quiz_id, student_department)
        ).fetchone()
        if not quiz:
            flash("This quiz is not available for your department")
            return redirect(url_for('student_practice_quizzes'))

        qcount = conn.execute(
            "SELECT COUNT(*) AS total FROM PracticeQuestions WHERE quiz_id=?",
            (quiz_id,)
        ).fetchone()
        total_questions = qcount['total'] if qcount else 0

        progress = conn.execute(
            """
            SELECT completed_at
            FROM PracticeProgress
            WHERE user_id=? AND quiz_id=?
            """,
            (user_id, quiz_id)
        ).fetchone()
        can_download = 1 if (progress and progress['completed_at']) else 0

    return render_template(
        'student/download_practice_quiz.html',
        quiz=quiz,
        total_questions=total_questions,
        can_download=can_download
    )


@app.route('/submit_practice_quiz/<int:quiz_id>', methods=['POST'])
@login_required
def submit_practice_quiz(quiz_id):
    if session.get('role') != 'Student':
        return redirect('/login')

    user_id = session['user_id']

    with get_db_connection() as conn:
        student_department_row = conn.execute(
            "SELECT COALESCE(NULLIF(department, ''), 'Computer') AS department FROM Users WHERE user_id=?",
            (session['user_id'],)
        ).fetchone()
        student_department = student_department_row['department'] if student_department_row else 'Computer'

        quiz = conn.execute(
            """
            SELECT p.*
            FROM Practice_Quizzes p
            LEFT JOIN Users u ON p.created_by = u.user_id
            WHERE p.quiz_id=?
              AND (',' || COALESCE(
                    NULLIF(p.target_departments, ''),
                    COALESCE(NULLIF(p.department, ''), COALESCE(NULLIF(u.department, ''), 'Computer'))
                  ) || ',') LIKE '%,' || ? || ',%'
            """,
            (quiz_id, student_department)
        ).fetchone()
        if not quiz:
            flash("This quiz is not available for your department")
            return redirect(url_for('student_practice_quizzes'))

        questions = conn.execute(
            "SELECT question_id FROM PracticeQuestions WHERE quiz_id=? ORDER BY question_id",
            (quiz_id,)
        ).fetchall()

        existing_first_attempt = conn.execute(
            """
            SELECT attempt_id
            FROM PracticeFirstAttempts
            WHERE user_id=? AND quiz_id=?
            LIMIT 1
            """,
            (user_id, quiz_id)
        ).fetchone()
        if existing_first_attempt:
            flash("Only your first practice quiz attempt is recorded for teacher reports.")
            return redirect(url_for('practice_quiz_results', quiz_id=quiz_id))

        total_questions = len(questions)
        correct_answers = 0

        # Keep only the latest answer set for this user+quiz.
        conn.execute(
            "DELETE FROM PracticeAnswers WHERE user_id=? AND quiz_id=?",
            (user_id, quiz_id)
        )

        for q in questions:
            question_id = q['question_id']
            selected_option_id = request.form.get(f'answer_{question_id}')
            selected_option_id = int(selected_option_id) if selected_option_id else None

            correct_option = conn.execute(
                """
                SELECT option_id
                FROM PracticeOptions
                WHERE question_id=? AND is_correct=1
                LIMIT 1
                """,
                (question_id,)
            ).fetchone()
            correct_option_id = correct_option['option_id'] if correct_option else None
            is_correct = 1 if selected_option_id and selected_option_id == correct_option_id else 0
            correct_answers += is_correct

            conn.execute(
                """
                INSERT INTO PracticeAnswers
                    (user_id, quiz_id, question_id, selected_option_id, is_correct, submitted_at)
                VALUES (?, ?, ?, ?, ?, datetime('now'))
                """,
                (user_id, quiz_id, question_id, selected_option_id, is_correct)
            )

        score = round((correct_answers / total_questions) * 100) if total_questions else 0

        try:
            conn.execute(
                """
                INSERT INTO PracticeProgress
                    (user_id, quiz_id, score, correct_answers, total_questions, completed_at, started_at)
                VALUES (?, ?, ?, ?, ?, datetime('now'), datetime('now'))
                ON CONFLICT(user_id, quiz_id) DO UPDATE SET
                    score=excluded.score,
                    correct_answers=excluded.correct_answers,
                    total_questions=excluded.total_questions,
                    completed_at=excluded.completed_at
                """,
                (user_id, quiz_id, score, correct_answers, total_questions)
            )
        except mysql.connector.Error as e:
            # Some legacy DBs have a broken FK on PracticeProgress.
            # Keep quiz answers saved even if progress upsert fails.
            print(f"Warning: PracticeProgress upsert skipped: {e}")

        conn.execute(
            """
            INSERT OR IGNORE INTO PracticeFirstAttempts
                (user_id, quiz_id, score, correct_answers, total_questions, attempted_at)
            VALUES (?, ?, ?, ?, ?, datetime('now'))
            """,
            (user_id, quiz_id, score, correct_answers, total_questions)
        )

    flash("Quiz submitted successfully")
    return redirect(url_for('practice_quiz_results', quiz_id=quiz_id))


@app.route('/practice_quiz_results/<int:quiz_id>')
@login_required
def practice_quiz_results(quiz_id):
    if session.get('role') != 'Student':
        return redirect('/login')

    user_id = session['user_id']

    with get_db_connection() as conn:
        student_department_row = conn.execute(
            "SELECT COALESCE(NULLIF(department, ''), 'Computer') AS department FROM Users WHERE user_id=?",
            (user_id,)
        ).fetchone()
        student_department = student_department_row['department'] if student_department_row else 'Computer'

        quiz = conn.execute(
            """
            SELECT p.*
            FROM Practice_Quizzes p
            LEFT JOIN Users u ON p.created_by = u.user_id
            WHERE p.quiz_id=?
              AND (',' || COALESCE(
                    NULLIF(p.target_departments, ''),
                    COALESCE(NULLIF(p.department, ''), COALESCE(NULLIF(u.department, ''), 'Computer'))
                  ) || ',') LIKE '%,' || ? || ',%'
            """,
            (quiz_id, student_department)
        ).fetchone()
        if not quiz:
            flash("This quiz is not available for your department")
            return redirect(url_for('student_practice_quizzes'))

        progress = conn.execute(
            """
            SELECT score, correct_answers, total_questions, completed_at
            FROM PracticeProgress
            WHERE user_id=? AND quiz_id=?
            """,
            (user_id, quiz_id)
        ).fetchone()

        results = conn.execute(
            """
            SELECT
                q.question_id,
                q.question_text,
                q.explanation,
                pa.is_correct,
                so.option_text AS selected_option,
                co.option_text AS correct_option
            FROM PracticeQuestions q
            LEFT JOIN PracticeAnswers pa
                ON pa.question_id = q.question_id
                AND pa.user_id = ?
                AND pa.quiz_id = ?
            LEFT JOIN PracticeOptions so ON so.option_id = pa.selected_option_id
            LEFT JOIN PracticeOptions co
                ON co.question_id = q.question_id
                AND co.is_correct = 1
            WHERE q.quiz_id = ?
            ORDER BY q.question_id
            """,
            (user_id, quiz_id, quiz_id)
        ).fetchall()

    if not progress:
        total = len(results)
        correct = sum(1 for r in results if r['is_correct'] == 1)
        score = round((correct / total) * 100) if total else 0
        progress = {
            'score': score,
            'correct_answers': correct,
            'total_questions': total,
            'completed_at': None
        }

    return render_template(
        'student/practice_quiz_results.html',
        quiz=quiz,
        progress=progress,
        results=results
    )

@app.route('/student_study_tools')
@login_required
def student_study_tools():
    if not _require_student():
        return redirect('/login')

    user_id = session['user_id']
    with get_db_connection() as conn:
        notes = conn.execute(
            "SELECT * FROM StudyNotes WHERE user_id=? ORDER BY updated_at DESC, note_id DESC",
            (user_id,)
        ).fetchall()
        flashcards = conn.execute(
            "SELECT * FROM Flashcards WHERE user_id=? ORDER BY card_id DESC",
            (user_id,)
        ).fetchall()
        goals = conn.execute(
            "SELECT * FROM DailyGoals WHERE user_id=? ORDER BY is_completed ASC, target_date ASC, goal_id DESC",
            (user_id,)
        ).fetchall()
        journal_logs = conn.execute(
            "SELECT * FROM StudyJournal WHERE user_id=? ORDER BY study_date DESC, journal_id DESC",
            (user_id,)
        ).fetchall()
        resources = conn.execute(
            "SELECT * FROM ResourceLibrary WHERE user_id=? ORDER BY resource_id DESC",
            (user_id,)
        ).fetchall()
        reminders = conn.execute(
            "SELECT * FROM StudyReminders WHERE user_id=? ORDER BY is_done ASC, due_date ASC, reminder_id DESC",
            (user_id,)
        ).fetchall()
        mind_maps = conn.execute(
            "SELECT * FROM MindMaps WHERE user_id=? ORDER BY updated_at DESC, map_id DESC",
            (user_id,)
        ).fetchall()
        assessments = conn.execute(
            "SELECT * FROM SelfAssessment WHERE user_id=? ORDER BY updated_at DESC, assessment_id DESC",
            (user_id,)
        ).fetchall()
        pomodoro_logs = conn.execute(
            "SELECT * FROM PomodoroLogs WHERE user_id=? ORDER BY log_id DESC LIMIT 20",
            (user_id,)
        ).fetchall()

    return render_template(
        'student/study_tools.html',
        notes=notes,
        flashcards=flashcards,
        goals=goals,
        journal_logs=journal_logs,
        resources=resources,
        reminders=reminders,
        mind_maps=mind_maps,
        assessments=assessments,
        pomodoro_logs=pomodoro_logs
    )

@app.route('/study/notes/add', methods=['POST'])
@login_required
def add_study_note():
    if not _require_student():
        return redirect('/login')
    title = (request.form.get('title') or '').strip()
    content = (request.form.get('content') or '').strip()
    if not title or not content:
        flash("Note title and content are required.")
        return redirect(url_for('student_study_tools'))
    with get_db_connection() as conn:
        conn.execute(
            """
            INSERT INTO StudyNotes (user_id, title, content, created_at, updated_at)
            VALUES (?, ?, ?, datetime('now'), datetime('now'))
            """,
            (session['user_id'], title, content)
        )
    flash("Note saved.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/notes/delete/<int:note_id>', methods=['POST'])
@login_required
def delete_study_note(note_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        conn.execute(
            "DELETE FROM StudyNotes WHERE note_id=? AND user_id=?",
            (note_id, session['user_id'])
        )
    flash("Note deleted.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/flashcards/add', methods=['POST'])
@login_required
def add_flashcard():
    if not _require_student():
        return redirect('/login')
    front_text = (request.form.get('front_text') or '').strip()
    back_text = (request.form.get('back_text') or '').strip()
    if not front_text or not back_text:
        flash("Flashcard front and back are required.")
        return redirect(url_for('student_study_tools'))
    with get_db_connection() as conn:
        conn.execute(
            "INSERT INTO Flashcards (user_id, front_text, back_text) VALUES (?, ?, ?)",
            (session['user_id'], front_text, back_text)
        )
    flash("Flashcard added.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/flashcards/delete/<int:card_id>', methods=['POST'])
@login_required
def delete_flashcard(card_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        conn.execute(
            "DELETE FROM Flashcards WHERE card_id=? AND user_id=?",
            (card_id, session['user_id'])
        )
    flash("Flashcard deleted.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/goals/add', methods=['POST'])
@login_required
def add_daily_goal():
    if not _require_student():
        return redirect('/login')
    goal_text = (request.form.get('goal_text') or '').strip()
    target_date = (request.form.get('target_date') or '').strip() or None
    if not goal_text:
        flash("Goal text is required.")
        return redirect(url_for('student_study_tools'))
    with get_db_connection() as conn:
        conn.execute(
            "INSERT INTO DailyGoals (user_id, goal_text, target_date) VALUES (?, ?, ?)",
            (session['user_id'], goal_text, target_date)
        )
    flash("Goal added.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/goals/toggle/<int:goal_id>', methods=['POST'])
@login_required
def toggle_daily_goal(goal_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        row = conn.execute(
            "SELECT is_completed FROM DailyGoals WHERE goal_id=? AND user_id=?",
            (goal_id, session['user_id'])
        ).fetchone()
        if row:
            conn.execute(
                "UPDATE DailyGoals SET is_completed=? WHERE goal_id=? AND user_id=?",
                (0 if row['is_completed'] else 1, goal_id, session['user_id'])
            )
    return redirect(url_for('student_study_tools'))

@app.route('/study/goals/delete/<int:goal_id>', methods=['POST'])
@login_required
def delete_daily_goal(goal_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        conn.execute(
            "DELETE FROM DailyGoals WHERE goal_id=? AND user_id=?",
            (goal_id, session['user_id'])
        )
    return redirect(url_for('student_study_tools'))

@app.route('/study/journal/add', methods=['POST'])
@login_required
def add_study_journal():
    if not _require_student():
        return redirect('/login')
    study_date = (request.form.get('study_date') or datetime.date.today().isoformat()).strip()
    topics = (request.form.get('topics') or '').strip()
    notes = (request.form.get('notes') or '').strip()
    try:
        minutes_spent = int(request.form.get('minutes_spent') or 0)
    except ValueError:
        minutes_spent = 0
    if not topics:
        flash("Topics are required for journal log.")
        return redirect(url_for('student_study_tools'))
    with get_db_connection() as conn:
        conn.execute(
            """
            INSERT INTO StudyJournal (user_id, study_date, minutes_spent, topics, notes)
            VALUES (?, ?, ?, ?, ?)
            """,
            (session['user_id'], study_date, max(0, minutes_spent), topics, notes)
        )
    flash("Journal entry added.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/journal/delete/<int:journal_id>', methods=['POST'])
@login_required
def delete_study_journal(journal_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        conn.execute(
            "DELETE FROM StudyJournal WHERE journal_id=? AND user_id=?",
            (journal_id, session['user_id'])
        )
    return redirect(url_for('student_study_tools'))

@app.route('/study/resources/add', methods=['POST'])
@login_required
def add_resource():
    if not _require_student():
        return redirect('/login')
    title = (request.form.get('title') or '').strip()
    resource_type = (request.form.get('resource_type') or 'link').strip().lower()
    url = (request.form.get('url') or '').strip()
    description = (request.form.get('description') or '').strip()
    if resource_type not in ('link', 'pdf', 'reference'):
        resource_type = 'link'
    if not title or not url:
        flash("Resource title and URL are required.")
        return redirect(url_for('student_study_tools'))
    with get_db_connection() as conn:
        conn.execute(
            """
            INSERT INTO ResourceLibrary (user_id, title, resource_type, url, description)
            VALUES (?, ?, ?, ?, ?)
            """,
            (session['user_id'], title, resource_type, url, description)
        )
    flash("Resource added.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/resources/delete/<int:resource_id>', methods=['POST'])
@login_required
def delete_resource(resource_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        conn.execute(
            "DELETE FROM ResourceLibrary WHERE resource_id=? AND user_id=?",
            (resource_id, session['user_id'])
        )
    return redirect(url_for('student_study_tools'))

@app.route('/study/reminders/add', methods=['POST'])
@login_required
def add_reminder():
    if not _require_student():
        return redirect('/login')
    title = (request.form.get('title') or '').strip()
    due_date = (request.form.get('due_date') or '').strip() or None
    if not title:
        flash("Reminder title is required.")
        return redirect(url_for('student_study_tools'))
    with get_db_connection() as conn:
        conn.execute(
            "INSERT INTO StudyReminders (user_id, title, due_date) VALUES (?, ?, ?)",
            (session['user_id'], title, due_date)
        )
    flash("Reminder added.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/reminders/toggle/<int:reminder_id>', methods=['POST'])
@login_required
def toggle_reminder(reminder_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        row = conn.execute(
            "SELECT is_done FROM StudyReminders WHERE reminder_id=? AND user_id=?",
            (reminder_id, session['user_id'])
        ).fetchone()
        if row:
            conn.execute(
                "UPDATE StudyReminders SET is_done=? WHERE reminder_id=? AND user_id=?",
                (0 if row['is_done'] else 1, reminder_id, session['user_id'])
            )
    return redirect(url_for('student_study_tools'))

@app.route('/study/reminders/delete/<int:reminder_id>', methods=['POST'])
@login_required
def delete_reminder(reminder_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        conn.execute(
            "DELETE FROM StudyReminders WHERE reminder_id=? AND user_id=?",
            (reminder_id, session['user_id'])
        )
    return redirect(url_for('student_study_tools'))

@app.route('/study/mindmaps/add', methods=['POST'])
@login_required
def add_mind_map():
    if not _require_student():
        return redirect('/login')
    title = (request.form.get('title') or '').strip()
    central_topic = (request.form.get('central_topic') or '').strip()
    related_topics = (request.form.get('related_topics') or '').strip()
    if not title or not central_topic:
        flash("Mind map title and central topic are required.")
        return redirect(url_for('student_study_tools'))
    with get_db_connection() as conn:
        conn.execute(
            """
            INSERT INTO MindMaps (user_id, title, central_topic, related_topics, created_at, updated_at)
            VALUES (?, ?, ?, ?, datetime('now'), datetime('now'))
            """,
            (session['user_id'], title, central_topic, related_topics)
        )
    flash("Mind map saved.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/mindmaps/delete/<int:map_id>', methods=['POST'])
@login_required
def delete_mind_map(map_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        conn.execute(
            "DELETE FROM MindMaps WHERE map_id=? AND user_id=?",
            (map_id, session['user_id'])
        )
    return redirect(url_for('student_study_tools'))

@app.route('/study/assessment/add', methods=['POST'])
@login_required
def add_assessment_item():
    if not _require_student():
        return redirect('/login')
    topic_name = (request.form.get('topic_name') or '').strip()
    status = (request.form.get('status') or 'learning').strip().lower()
    notes = (request.form.get('notes') or '').strip()
    if status not in ('strong', 'learning', 'revise'):
        status = 'learning'
    if not topic_name:
        flash("Topic name is required.")
        return redirect(url_for('student_study_tools'))
    with get_db_connection() as conn:
        conn.execute(
            """
            INSERT INTO SelfAssessment (user_id, topic_name, status, notes, created_at, updated_at)
            VALUES (?, ?, ?, ?, datetime('now'), datetime('now'))
            """,
            (session['user_id'], topic_name, status, notes)
        )
    flash("Checklist item added.")
    return redirect(url_for('student_study_tools'))

@app.route('/study/assessment/delete/<int:assessment_id>', methods=['POST'])
@login_required
def delete_assessment_item(assessment_id):
    if not _require_student():
        return redirect('/login')
    with get_db_connection() as conn:
        conn.execute(
            "DELETE FROM SelfAssessment WHERE assessment_id=? AND user_id=?",
            (assessment_id, session['user_id'])
        )
    return redirect(url_for('student_study_tools'))

@app.route('/study/pomodoro/log', methods=['POST'])
@login_required
def log_pomodoro():
    if not _require_student():
        return redirect('/login')
    try:
        focus_minutes = int(request.form.get('focus_minutes') or 25)
    except ValueError:
        focus_minutes = 25
    try:
        break_minutes = int(request.form.get('break_minutes') or 5)
    except ValueError:
        break_minutes = 5
    try:
        cycles_completed = int(request.form.get('cycles_completed') or 1)
    except ValueError:
        cycles_completed = 1

    with get_db_connection() as conn:
        conn.execute(
            """
            INSERT INTO PomodoroLogs (user_id, focus_minutes, break_minutes, cycles_completed)
            VALUES (?, ?, ?, ?)
            """,
            (session['user_id'], max(1, focus_minutes), max(1, break_minutes), max(1, cycles_completed))
        )
    flash("Pomodoro session logged.")
    return redirect(url_for('student_study_tools'))

@app.route('/student_dashboard')
def student_dashboard():

    if 'user_id' not in session or session.get('role') != 'Student':
        return redirect('/login')

    # ❌ NO quiz fetching here
    return render_template('student/dashboard.html')

@app.route('/settings')
@login_required
def settings():
    user_id = session['user_id']
    with get_db_connection() as conn:
        user = conn.execute(
            """
            SELECT username, email, role,
                   COALESCE(theme_mode, 'light') AS theme_mode,
                   COALESCE(font_scale, 'medium') AS font_scale,
                   COALESCE(app_language, 'en') AS app_language,
                   COALESCE(email_alerts, 1) AS email_alerts,
                   COALESCE(mute_notifications, 0) AS mute_notifications
            FROM Users
            WHERE user_id=?
            """,
            (user_id,)
        ).fetchone()

    if not user:
        session.clear()
        flash("Account not found. Please login again.")
        return redirect(url_for('login'))

    return render_template('shared/settings.html', user=user)

@app.route('/settings/profile', methods=['POST'])
@login_required
def update_profile():
    user_id = session['user_id']
    username = (request.form.get('username') or '').strip()
    email = (request.form.get('email') or '').strip().lower()

    if not username:
        flash("Username is required.")
        return redirect(url_for('settings'))
    if not _valid_email(email):
        flash("Please enter a valid email address.")
        return redirect(url_for('settings'))

    with get_db_connection() as conn:
        existing = conn.execute(
            "SELECT user_id FROM Users WHERE email=? AND user_id<>?",
            (email, user_id)
        ).fetchone()
        if existing:
            flash("Email is already used by another account.")
            return redirect(url_for('settings'))

        conn.execute(
            "UPDATE Users SET username=?, email=? WHERE user_id=?",
            (username, email, user_id)
        )

    session['username'] = username
    flash("Profile updated successfully.")
    return redirect(url_for('settings'))

@app.route('/settings/password', methods=['POST'])
@login_required
def update_password():
    user_id = session['user_id']
    current_password = request.form.get('current_password') or ''
    new_password = request.form.get('new_password') or ''
    confirm_password = request.form.get('confirm_password') or ''

    if not current_password or not new_password or not confirm_password:
        flash("All password fields are required.")
        return redirect(url_for('settings'))
    if new_password != confirm_password:
        flash("New password and confirm password do not match.")
        return redirect(url_for('settings'))
    if not is_password_strong(new_password):
        flash("Weak password. Use at least 8 chars with letters, numbers, and a symbol.")
        return redirect(url_for('settings'))

    with get_db_connection() as conn:
        user = conn.execute("SELECT password FROM Users WHERE user_id=?", (user_id,)).fetchone()
        if not user or not check_password_hash(user['password'], current_password):
            flash("Current password is incorrect.")
            return redirect(url_for('settings'))

        conn.execute(
            "UPDATE Users SET password=? WHERE user_id=?",
            (generate_password_hash(new_password), user_id)
        )

    flash("Password updated successfully.")
    return redirect(url_for('settings'))

@app.route('/settings/appearance', methods=['POST'])
@login_required
def update_appearance():
    user_id = session['user_id']
    theme_mode = (request.form.get('theme_mode') or 'light').strip().lower()
    font_scale = (request.form.get('font_scale') or 'medium').strip().lower()
    app_language = (request.form.get('app_language') or 'en').strip().lower()

    if theme_mode not in ('light', 'dark'):
        theme_mode = 'light'
    if font_scale not in ('small', 'medium', 'large'):
        font_scale = 'medium'
    if app_language not in ('en', 'mr'):
        app_language = 'en'

    with get_db_connection() as conn:
        conn.execute(
            """
            UPDATE Users
            SET theme_mode=?, font_scale=?, app_language=?
            WHERE user_id=?
            """,
            (theme_mode, font_scale, app_language, user_id)
        )

    session['theme_mode'] = theme_mode
    session['font_scale'] = font_scale
    session['app_language'] = app_language
    session['tip_language'] = app_language

    flash("Appearance and language settings saved.")
    return redirect(url_for('settings'))

@app.route('/settings/notifications', methods=['POST'])
@login_required
def update_notifications():
    user_id = session['user_id']
    email_alerts = _to_int_flag(request.form.get('email_alerts'))
    mute_notifications = _to_int_flag(request.form.get('mute_notifications'))

    with get_db_connection() as conn:
        conn.execute(
            """
            UPDATE Users
            SET email_alerts=?, mute_notifications=?
            WHERE user_id=?
            """,
            (email_alerts, mute_notifications, user_id)
        )

    session['email_alerts'] = email_alerts
    session['mute_notifications'] = mute_notifications
    flash("Notification settings updated.")
    return redirect(url_for('settings'))

@app.route('/settings/logout_all_devices', methods=['POST'])
@login_required
def logout_all_devices():
    user_id = session['user_id']
    with get_db_connection() as conn:
        conn.execute(
            "UPDATE Users SET session_version = COALESCE(session_version, 0) + 1 WHERE user_id=?",
            (user_id,)
        )

    session.clear()
    flash("Logged out from all devices.")
    return redirect(url_for('login'))

@app.route('/settings/delete_account', methods=['POST'])
@login_required
def delete_account():
    user_id = session['user_id']
    current_password = request.form.get('current_password') or ''

    if not current_password:
        flash("Please enter your current password to delete account.")
        return redirect(url_for('settings'))

    try:
        with get_db_connection() as conn:
            user = conn.execute("SELECT password FROM Users WHERE user_id=?", (user_id,)).fetchone()
            if not user or not check_password_hash(user['password'], current_password):
                flash("Current password is incorrect.")
                return redirect(url_for('settings'))

            _delete_user_account(conn, user_id)
    except Exception as e:
        print("Delete account error:", e)
        flash("Could not delete account right now. Please try again.")
        return redirect(url_for('settings'))

    session.clear()
    flash("Account deleted successfully.")
    return redirect(url_for('login'))

@app.route('/daily_learning')
@login_required
def daily_learning():
    return render_template('shared/daily_learning.html')

@app.route('/api/daily_tip')
@login_required
def api_daily_tip():
    user_id = session['user_id']
    role = session.get('role', 'Student')
    requested_lang = (request.args.get('lang') or session.get('app_language') or session.get('tip_language') or 'en').strip().lower()
    if requested_lang not in ('en', 'hi', 'mr'):
        requested_lang = 'en'
    session['tip_language'] = requested_lang

    with get_db_connection() as conn:
        tip, inferred_subject, inferred_difficulty, final_lang = get_daily_tip_for_user(
            conn, user_id, role, requested_lang
        )
        if not tip:
            return jsonify({"ok": False, "message": "No tip available"}), 404

        today = datetime.date.today().isoformat()
        existing_view = conn.execute("""
            SELECT view_id, reward_points
            FROM UserTipViews
            WHERE user_id=? AND viewed_on=?
        """, (user_id, today)).fetchone()

        just_recorded = False
        if not existing_view:
            conn.execute("""
                INSERT OR IGNORE INTO UserTipViews (user_id, tip_id, viewed_on, reward_points)
                VALUES (?, ?, ?, 0)
            """, (user_id, tip["tip_id"], today))
            just_recorded = True

        streak = _calculate_tip_streak(conn, user_id)
        reward_today = 0
        if just_recorded and streak > 0 and streak % 7 == 0:
            reward_today = 25
            conn.execute("""
                UPDATE UserTipViews
                SET reward_points=?
                WHERE user_id=? AND viewed_on=?
            """, (reward_today, user_id, today))
        elif existing_view:
            reward_today = existing_view["reward_points"] or 0

        total_reward_points = conn.execute("""
            SELECT COALESCE(SUM(reward_points), 0) AS total_points
            FROM UserTipViews
            WHERE user_id=?
        """, (user_id,)).fetchone()["total_points"]

    share_text = f"Daily {tip['content_type'].title()}: {tip['content_text']}"
    share_url = "https://twitter.com/intent/tweet?text=" + urllib.parse.quote(share_text)

    return jsonify({
        "ok": True,
        "tip": {
            "id": tip["tip_id"],
            "text": tip["content_text"],
            "type": tip["content_type"],
            "subject": tip["subject"],
            "difficulty": tip["difficulty_level"],
            "language": tip["language"]
        },
        "meta": {
            "inferred_subject": inferred_subject,
            "adaptive_difficulty": inferred_difficulty,
            "language": final_lang
        },
        "gamification": {
            "streak": streak,
            "reward_today": reward_today,
            "total_reward_points": total_reward_points
        },
        "share": {
            "text": share_text,
            "twitter_intent_url": share_url
        }
    })

@app.route('/join_quiz', methods=['GET', 'POST'])
def join_quiz():
    if request.method == 'POST':
        pin = request.form.get('pin')
        nickname = (request.form.get('nickname') or '').strip()

        if not pin or not nickname:
            flash("PIN and Nickname are required")
            return redirect('/join_quiz')

        conn = get_db_connection()

        # Check if PIN exists
        session_data = conn.execute(
            "SELECT session_id, quiz_id FROM live_sessions WHERE pin = ? AND is_active = 1",
            (pin,)
        ).fetchone()

        if not session_data:
            flash("Invalid PIN")
            conn.close()
            return redirect('/join_quiz')

        session_id = session_data['session_id']
        quiz_id = session_data['quiz_id']

        nickname_exists = conn.execute(
            "SELECT 1 FROM participants WHERE session_id=? AND nickname=? LIMIT 1",
            (session_id, nickname)
        ).fetchone()
        if nickname_exists:
            flash("Nickname already taken in this quiz. Please choose another nickname.")
            conn.close()
            return redirect('/join_quiz')

        # Insert student into participants table
        try:
            conn.execute(
                "INSERT INTO participants (session_id, nickname) VALUES (?, ?)",
                (session_id, nickname)
            )
            conn.commit()
        except mysql.connector.IntegrityError:
            conn.close()
            flash("Nickname already taken in this live quiz.")
            return redirect('/join_quiz')
        conn.close()

        # Store student info in session for quiz page
        session['student_nickname'] = nickname
        session['session_id'] = session_id
        session['quiz_id'] = quiz_id

        # Redirect to student quiz page
        return redirect(url_for('student_waiting', session_id=session_id, player=nickname))

    return render_template('student/join_quiz.html')




    return render_template('student/live_quiz.html', quiz_questions=quiz_questions, session_id=session_id)
@app.route('/host_lobby/<int:session_id>')
def host_lobby(session_id):
    if 'role' not in session or session['role'] != 'Teacher':
        flash("Please login as teacher")
        return redirect('/login')

    conn = get_db_connection()

    # Get PIN for the session
    session_data = conn.execute(
        "SELECT pin FROM live_sessions WHERE session_id = ?", 
        (session_id,)
    ).fetchone()
    if not session_data:
        flash("Session not found")
        return redirect('/teacher_dashboard')
    pin = session_data['pin']

    # Get students who joined (empty initially)
    students = conn.execute(
        "SELECT nickname FROM participants WHERE session_id = ?", 
        (session_id,)
    ).fetchall()

    conn.close()

    return render_template('teacher/waiting_room.html', pin=pin, students=students, session_id=session_id)

@app.route('/student_waiting/<int:session_id>')
def student_waiting(session_id):
    player_name = (request.args.get('player') or session.get('student_nickname') or '').strip()
    if not player_name:
        flash("Please enter PIN and nickname first")
        return redirect('/join_quiz')

    conn = get_db_connection()
    
    # Verify session exists
    session_data = conn.execute(
        "SELECT ls.pin, q.quiz_name FROM live_sessions ls "
        "JOIN Quizzes q ON ls.quiz_id = q.quiz_id "
        "WHERE ls.session_id = ? AND ls.is_active = 1",
        (session_id,)
    ).fetchone()
    conn.close()

    if not session_data:
        flash("Invalid or inactive session")
        return redirect('/join_quiz')
    return render_template(
        'student/student_waiting.html',
        session=session,
        player_name=player_name,
        session_id=session_id,
        pin=session_data['pin'],
        quiz_name=session_data['quiz_name']
    )


# Waiting room page
@app.route('/waiting_room/<int:session_id>')
def waiting_room(session_id):
    if 'role' not in session or session['role'] != 'Teacher':
        flash("Please login as teacher")
        return redirect('/login')

    conn = get_db_connection()
    session_data = conn.execute(
        "SELECT ls.pin, q.quiz_name FROM live_sessions ls "
        "JOIN Quizzes q ON ls.quiz_id = q.quiz_id "
        "WHERE ls.session_id = ?", (session_id,)
    ).fetchone()

    students = conn.execute(
        "SELECT nickname FROM participants WHERE session_id = ?", (session_id,)
    ).fetchall()
    conn.close()

    return render_template(
        'teacher/waiting_room.html',
        session_id=session_id,
        pin=session_data['pin'],
        quiz_name=session_data['quiz_name'],
        students=students
    )


# API to fetch joined students
@app.route('/get_students/<int:session_id>')
def get_students(session_id):
    conn = get_db_connection()
    students = conn.execute(
        "SELECT nickname FROM participants WHERE session_id = ?", (session_id,)
    ).fetchall()
    conn.close()
    return {"students": [dict(s) for s in students]}




@app.route('/leave_quiz', methods=['POST'])
def leave_quiz():
    if 'student_nickname' not in session or 'session_id' not in session:
        flash("You are not in any quiz")
        return redirect(url_for('student_dashboard'))  # <-- use url_for

    nickname = session['student_nickname']
    session_id = session['session_id']

    conn = get_db_connection()
    conn.execute(
        "DELETE FROM participants WHERE session_id = ? AND nickname = ?",
        (session_id, nickname)
    )
    conn.commit()
    conn.close()

    # Clear student session
    session.pop('student_nickname', None)
    session.pop('session_id', None)

    flash("You have left the quiz")
    return redirect(url_for('student_dashboard'))  # <-- use url_for



# ---------------- LOGOUT ----------------
@app.route('/logout')
def logout():
    session.clear()
    flash("Logged out successfully")
    return redirect('/login')






@app.route('/teacher_live_quiz/<int:session_id>')
def teacher_live_quiz(session_id):
    if 'role' not in session or session['role'] != 'Teacher':
        flash("Please login as teacher")
        return redirect('/login')

    conn = get_db_connection()
    session_data = conn.execute(
        "SELECT * FROM live_sessions WHERE session_id=?",
        (session_id,)
    ).fetchone()

    if not session_data:
        conn.close()
        flash("Session not found")
        return redirect('/teacher_dashboard')

    live_state = _get_live_question_state(conn, session_data)
    total_questions_row = conn.execute(
        "SELECT COUNT(*) AS total FROM questions WHERE quiz_id=?",
        (session_data["quiz_id"],)
    ).fetchone()
    total_questions = total_questions_row["total"] if total_questions_row else 0
    has_next = (session_data["current_question"] + 1) < total_questions

    options = []
    answer_stats = {}
    question_ranking = {"top3": [], "rows": []}
    has_active_question = live_state.get("started") and not live_state.get("finished")
    if has_active_question:
        options = conn.execute(
            "SELECT option_text, is_correct FROM options WHERE question_id=? ORDER BY option_id",
            (live_state["question_id"],)
        ).fetchall()
        answer_stats = _get_answer_breakdown(conn, session_id, live_state["question_id"])
        question_ranking = _get_question_ranking(conn, session_id, live_state["question_id"])

    conn.close()

    return render_template(
        "teacher/live_question.html",
        session_id=session_id,
        question=live_state if has_active_question else None,
        options=options,
        answer_stats=answer_stats,
        question_ranking=question_ranking,
        has_next=has_next,
        total_questions=total_questions
    )





@app.route('/next_question/<int:session_id>')
def next_question(session_id):
    if 'role' not in session or session['role'] != 'Teacher':
        flash("Please login as teacher")
        return redirect('/login')

    conn = get_db_connection()
    session_data = conn.execute(
        "SELECT quiz_id, current_question FROM live_sessions WHERE session_id=?",
        (session_id,)
    ).fetchone()
    if not session_data:
        conn.close()
        flash("Session not found")
        return redirect('/teacher_dashboard')

    total_row = conn.execute(
        "SELECT COUNT(*) AS total FROM questions WHERE quiz_id=?",
        (session_data["quiz_id"],)
    ).fetchone()
    total_questions = total_row["total"] if total_row else 0
    next_index = (session_data["current_question"] or 0) + 1

    if next_index >= total_questions:
        conn.execute(
            "UPDATE live_sessions SET current_question=?, is_active=0 WHERE session_id=?",
            (next_index, session_id)
        )
        conn.commit()
        conn.close()
        return redirect(url_for('final_podium', session_id=session_id))

    conn.execute("""
        UPDATE live_sessions
        SET current_question = ?,
            question_started_at = datetime('now')
        WHERE session_id=?
    """, (next_index, session_id))

    conn.commit()
    conn.close()

    return redirect(url_for('teacher_live_quiz', session_id=session_id))


@app.route('/student_live_quiz/<int:session_id>')
def student_live_quiz(session_id):
    player_name = (request.args.get('player') or session.get('student_nickname') or '').strip()
    if not player_name:
        return redirect('/join_quiz')

    return render_template(
        'student/live_question.html',
        session_id=session_id,
        player_name=player_name
    )


@app.route('/start_live_quiz/<int:session_id>', methods=['POST'])
def start_live_quiz(session_id):
    with get_db_connection() as conn:
        conn.execute("DELETE FROM player_answers WHERE session_id=?", (session_id,))
        conn.execute("DELETE FROM PlayerScores WHERE session_id=?", (session_id,))
        conn.execute("""
            UPDATE live_sessions
            SET started = 1,
                current_question = 0,
                start_time = datetime('now'),
                question_started_at = datetime('now'),
                is_active = 1
            WHERE session_id = ?
        """, (session_id,))
    return jsonify({"success": True})




@app.route('/submit_answer', methods=['POST'])
def submit_answer():
    data = request.json
    session_id = data.get('session_id')
    player_name = (data.get('player_name') or '').strip() or session.get('student_nickname')
    answer = data.get('answer')

    if not session_id or not player_name or answer is None:
        return jsonify({"success": False, "message": "Invalid submission"}), 400

    conn = get_db_connection()

    participant_exists = conn.execute(
        "SELECT 1 FROM participants WHERE session_id=? AND nickname=? LIMIT 1",
        (session_id, player_name)
    ).fetchone()
    if not participant_exists:
        conn.close()
        return jsonify({"success": False, "message": "Participant not found in session"}), 403

    # current question
    session_data = conn.execute(
        "SELECT * FROM live_sessions WHERE session_id=?",
        (session_id,)
    ).fetchone()
    if not session_data:
        conn.close()
        return jsonify({"success": False, "message": "Session not found"}), 404

    live_state = _get_live_question_state(conn, session_data)
    if live_state.get("finished") or not live_state.get("started"):
        conn.close()
        return jsonify({"success": False, "message": "Question not active"}), 400

    question_id = live_state["question_id"]
    question_index = live_state["question_index"]
    time_limit = live_state["time_limit"]
    question_started_at = _parse_db_datetime(session_data["question_started_at"]) or datetime.datetime.utcnow()
    response_ms = max(0, int((datetime.datetime.utcnow() - question_started_at).total_seconds() * 1000))

    existing = conn.execute(
        """
        SELECT is_correct, score_awarded, response_ms
        FROM player_answers
        WHERE session_id=? AND question_id=? AND player_name=?
        LIMIT 1
        """,
        (session_id, question_id, player_name)
    ).fetchone()
    if existing:
        rank_details = _get_player_live_rank_details(conn, session_id, player_name)
        conn.close()
        return jsonify({
            "success": True,
            "already_submitted": True,
            "correct": bool(existing["is_correct"]),
            "score": existing["score_awarded"],
            "response_ms": existing["response_ms"],
            "question_id": question_id,
            "rank": rank_details["rank"],
            "total_players": rank_details["total_players"],
            "total_score": rank_details["score"],
            "points_to_next": rank_details["points_to_next"],
            "next_player": rank_details["next_player"]
        })

    option_row = conn.execute(
        "SELECT is_correct FROM options WHERE question_id=? AND option_text=?",
        (question_id, answer)
    ).fetchone()
    raw_correct = 1 if option_row and option_row["is_correct"] == 1 else 0
    in_time = response_ms <= (time_limit * 1000)
    is_correct = 1 if (raw_correct and in_time) else 0

    if is_correct:
        remaining_ms = max(0, (time_limit * 1000) - response_ms)
        score = int(200 + (800 * (remaining_ms / max(1, time_limit * 1000))))
    else:
        score = 0

    conn.execute("""
        INSERT OR IGNORE INTO player_answers (
            session_id, question_id, question_index, player_name, answer,
            is_correct, response_ms, score_awarded
        )
        VALUES (?,?,?,?,?,?,?,?)
    """, (session_id, question_id, question_index, player_name, answer, is_correct, response_ms, score))

    # If ignored due to duplicate (race/refresh), return existing saved row.
    persisted = conn.execute(
        """
        SELECT is_correct, score_awarded, response_ms
        FROM player_answers
        WHERE session_id=? AND question_id=? AND player_name=?
        LIMIT 1
        """,
        (session_id, question_id, player_name)
    ).fetchone()
    final_correct = bool(persisted["is_correct"]) if persisted else bool(is_correct)
    final_score = persisted["score_awarded"] if persisted else score
    final_response_ms = persisted["response_ms"] if persisted else response_ms

    rank_details = _get_player_live_rank_details(conn, session_id, player_name)
    conn.commit()
    conn.close()

    return jsonify({
        "success": True,
        "correct": final_correct,
        "score": final_score,
        "response_ms": final_response_ms,
        "question_id": question_id,
        "rank": rank_details["rank"],
        "total_players": rank_details["total_players"],
        "total_score": rank_details["score"],
        "points_to_next": rank_details["points_to_next"],
        "next_player": rank_details["next_player"]
    })



@app.route('/check_quiz_started/<int:session_id>')
def check_quiz_started(session_id):
    with get_db_connection() as conn:
        row = conn.execute(
            "SELECT started FROM live_sessions WHERE session_id=?",
            (session_id,)
        ).fetchone()

    return jsonify({"started": row["started"] == 1})


@app.route('/get_current_question/<int:session_id>')
def get_current_question(session_id):

    conn = get_db_connection()

    session_data = conn.execute(
        "SELECT * FROM live_sessions WHERE session_id=?",
        (session_id,)
    ).fetchone()

    if not session_data:
        conn.close()
        return jsonify({"finished": True, "started": False})

    live_state = _get_live_question_state(conn, session_data)
    viewer_name = (request.args.get('player_name') or '').strip() or session.get('student_nickname')

    if live_state.get("finished"):
        final_url = url_for('final_podium', session_id=session_id)
        if viewer_name:
            final_url = url_for('final_podium', session_id=session_id, player=viewer_name)
        conn.close()
        return jsonify({
            "finished": True,
            "started": True,
            "leaderboard_url": final_url
        })

    live_state["leaderboard_url"] = url_for('live_leaderboard', session_id=session_id)
    if viewer_name and live_state.get("question_id"):
        your_row = _get_player_question_answer(conn, session_id, live_state["question_id"], viewer_name)
        rank_details = _get_player_live_rank_details(conn, session_id, viewer_name)
        live_state["your_name"] = viewer_name
        live_state["your_submitted"] = bool(your_row)
        live_state["your_answer"] = your_row["answer"] if your_row else None
        live_state["your_correct"] = bool(your_row["is_correct"]) if your_row else None
        live_state["your_response_ms"] = your_row["response_ms"] if your_row else None
        live_state["your_score_awarded"] = your_row["score_awarded"] if your_row else None
        live_state["your_rank"] = rank_details["rank"]
        live_state["your_total_players"] = rank_details["total_players"]
        live_state["your_total_score"] = rank_details["score"]
        live_state["your_points_to_next"] = rank_details["points_to_next"]
        live_state["your_next_player"] = rank_details["next_player"]

    if live_state["phase"] == "reveal":
        live_state["answer_stats"] = _get_answer_breakdown(conn, session_id, live_state["question_id"])
        live_state["question_ranking"] = _get_question_ranking(conn, session_id, live_state["question_id"])

    conn.close()
    return jsonify(live_state)


@app.route('/live_leaderboard/<int:session_id>')
def live_leaderboard(session_id):
    if session.get('role') != 'Teacher':
        return redirect('/login')

    with get_db_connection() as conn:
        session_data = conn.execute(
            "SELECT * FROM live_sessions WHERE session_id=?",
            (session_id,)
        ).fetchone()
        if not session_data:
            flash("Session not found")
            return redirect('/teacher_dashboard')

        quiz_row = conn.execute(
            "SELECT quiz_name FROM quizzes WHERE quiz_id=?",
            (session_data["quiz_id"],)
        ).fetchone()
        total_row = conn.execute(
            "SELECT COUNT(*) AS total FROM questions WHERE quiz_id=?",
            (session_data["quiz_id"],)
        ).fetchone()
        scores = _get_live_leaderboard_rows(conn, session_id)
        current_question_row = conn.execute(
            "SELECT question_id FROM questions WHERE quiz_id=? LIMIT 1 OFFSET ?",
            (session_data["quiz_id"], session_data["current_question"] or 0)
        ).fetchone()
        question_ranking = {"top3": [], "rows": []}
        if current_question_row:
            question_ranking = _get_question_ranking(conn, session_id, current_question_row["question_id"])

    total_questions = total_row["total"] if total_row else 0
    current_display = min((session_data["current_question"] or 0) + 1, total_questions if total_questions > 0 else 1)
    role = 'Teacher' if session.get('role') == 'Teacher' else 'Student'
    return render_template(
        'shared/live_leaderboard.html',
        session_id=session_id,
        role=role,
        scores=scores,
        question_ranking=question_ranking,
        quiz_name=quiz_row["quiz_name"] if quiz_row else "Live Quiz",
        current_question=current_display,
        total_questions=total_questions
    )

@app.route('/final_podium/<int:session_id>')
def final_podium(session_id):
    if 'role' not in session and 'student_nickname' not in session:
        return redirect('/login')

    with get_db_connection() as conn:
        session_row = conn.execute(
            "SELECT quiz_id FROM live_sessions WHERE session_id=?",
            (session_id,)
        ).fetchone()
        if not session_row:
            flash("Session not found")
            return redirect('/student_dashboard')

        scores = _get_live_leaderboard_rows(conn, session_id)

    default_avatar = url_for('static', filename='avatars/default.png')
    podium = []
    for row in scores[:3]:
        podium.append({
            "player_name": row["player_name"],
            "score": row["score"],
            "avatar": default_avatar
        })

    role = 'Teacher' if session.get('role') == 'Teacher' else 'Student'
    student_result = None
    if role == 'Student':
        player_name = (
            request.args.get('player')
            or session.get('student_nickname')
            or session.get('username')
            or ''
        ).strip()
        if player_name:
            target_name = player_name.lower()
            for idx, row in enumerate(scores):
                row_name = (row["player_name"] or "").strip()
                if row_name.lower() == target_name:
                    rank = idx + 1
                    if rank <= 3:
                        message = "Well played!"
                    else:
                        message = "Better luck next time."
                    student_result = {
                        "player_name": row_name or player_name,
                        "rank": rank,
                        "total_players": len(scores),
                        "score": row["score"],
                        "message": message
                    }
                    break
        if not student_result:
            # Keep student result card visible even when nickname mapping fails.
            student_result = {
                "player_name": player_name or "Student",
                "rank": None,
                "total_players": len(scores),
                "score": 0,
                "message": "Well played!"
            }

    return render_template(
        'shared/final_podium.html',
        session_id=session_id,
        podium=podium,
        role=role,
        student_result=student_result
    )


@app.route('/live_leaderboard_data/<int:session_id>')
def live_leaderboard_data(session_id):
    with get_db_connection() as conn:
        session_data = conn.execute(
            "SELECT current_question, quiz_id FROM live_sessions WHERE session_id=?",
            (session_id,)
        ).fetchone()
        if not session_data:
            return jsonify({"success": False, "message": "Session not found"}), 404

        total_row = conn.execute(
            "SELECT COUNT(*) AS total FROM questions WHERE quiz_id=?",
            (session_data["quiz_id"],)
        ).fetchone()
        scores = _get_live_leaderboard_rows(conn, session_id)
        current_question_row = conn.execute(
            "SELECT question_id FROM questions WHERE quiz_id=? LIMIT 1 OFFSET ?",
            (session_data["quiz_id"], session_data["current_question"] or 0)
        ).fetchone()
        question_ranking = {"top3": [], "rows": []}
        if current_question_row:
            question_ranking = _get_question_ranking(conn, session_id, current_question_row["question_id"])
        total_questions = total_row["total"] if total_row else 0
        current_display = min((session_data["current_question"] or 0) + 1, total_questions if total_questions > 0 else 1)

    return jsonify({
        "success": True,
        "scores": scores,
        "question_ranking": question_ranking,
        "current_question": current_display,
        "total_questions": total_questions
    })

@app.route('/get_answer_counts/<int:session_id>/<int:question_id>')
def get_answer_counts(session_id, question_id):
    with get_db_connection() as conn:
        breakdown = _get_answer_breakdown(conn, session_id, question_id)
    return jsonify(breakdown)

@app.route('/get_question_ranking/<int:session_id>/<int:question_id>')
def get_question_ranking(session_id, question_id):
    with get_db_connection() as conn:
        ranking = _get_question_ranking(conn, session_id, question_id)
    return jsonify(ranking)


migrate_practice_tables()
init_practice_table()

# ---------------- RUN APP ----------------
if __name__ == '__main__':
    migrate_practice_tables()
    init_practice_table()
    app.run(host="0.0.0.0", port=5000,debug=True)
