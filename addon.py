# Code created by Siddharth Ahuja: www.github.com/ahujasid © 2025

import re
import bpy
import mathutils
import json
import threading
import socket
import queue
import time
import traceback
import os
import uuid
import zlib
from bpy.props import IntProperty, BoolProperty
import io
import hashlib
from collections import deque
from contextlib import contextmanager, redirect_stdout, suppress
from bpy.app.handlers import persistent

bl_info = {
    "name": "Blender MCP",
    "author": "BlenderMCP",
    "version": (1, 5),
    "blender": (3, 0, 0),
    "location": "View3D > Sidebar > BlenderMCP",
    "description": "Connect Blender to Claude via MCP",
    "category": "Interface",
}

# Keep in sync with blender_mcp.addon_manager.EXPECTED_ADDON_PROTOCOL_VERSION.
ADDON_PROTOCOL_VERSION = 6

# Per-snapshot object cap for get_world_state_snapshot. Keep in sync with
# blender_mcp.trajectory.MAX_SNAPSHOT_OBJECTS.
MAX_SNAPSHOT_OBJECTS = 2000

# Selected-name cap for get_world_state_snapshot: select-all in a large scene
# would otherwise make `selected` the dominant field of both step snapshots.
# Keep in sync with blender_mcp.trajectory.MAX_SNAPSHOT_SELECTED.
MAX_SNAPSHOT_SELECTED = 200

#region Manual edit capture
# Records what the human does in Blender while an MCP session is live.

MAX_EDIT_EVENTS = 256

# Operators that fire constantly during interactive work and carry no meaningful
# intent on their own.
_IGNORED_OPERATORS = frozenset({
    "view3d.rotate",
    "view3d.move",
    "view3d.zoom",
    "view3d.dolly",
    "view3d.view_axis",
    "view3d.view_orbit",
    "view3d.view_pan",
    "view3d.smoothview",
    "view3d.cursor3d",
    "wm.tool_set_by_id",
    "wm.context_set_value",
    "screen.animation_step",
})

# Operator properties holding filesystem paths. Never recorded.
_PATH_PROPERTY_NAMES = frozenset({
    "filepath",
    "filename",
    "directory",
    "filepath_raw",
    "relpath",
})
_PATH_PROPERTY_SUBSTRINGS = ("filepath", "filename", "directory", "_dir", "path")
MAX_OPERATOR_PROPERTY_CHARS = 200

# depsgraph_update_post fires on every scene update, many times per second
# during interactive drags.
EDIT_POLL_MIN_INTERVAL = 0.1


def _is_path_property(identifier):
    """True if an operator property likely holds a filesystem path."""
    lowered = identifier.lower()
    if lowered in _PATH_PROPERTY_NAMES:
        return True
    return any(token in lowered for token in _PATH_PROPERTY_SUBSTRINGS)


class UserEditRecorder:
    """Buffers human-originated operator and undo events for the MCP server.

    Anything that happens while an agent command is running is attributed to
    the agent, not the human; `agent_command()` brackets that window.
    """

    def __init__(self):
        self._events = deque(maxlen=MAX_EDIT_EVENTS)
        self._agent_depth = 0
        self._last_operator_count = 0
        self._seen_baseline = False
        self._last_poll_time = 0.0

    @contextmanager
    def agent_command(self):
        """Suppress capture for the duration of an agent-issued command."""
        self._agent_depth += 1
        try:
            yield
        finally:
            self._agent_depth = max(0, self._agent_depth - 1)
            self._resync_operator_baseline()

    @property
    def _suppressed(self):
        return self._agent_depth > 0

    def _operator_stack(self):
        try:
            return list(bpy.context.window_manager.operators)
        except Exception:
            return []

    def _resync_operator_baseline(self):
        self._last_operator_count = len(self._operator_stack())
        self._seen_baseline = True

    def poll_operators(self, now=None):
        """Emit rows for operators run since the last poll. Main thread only.

        Throttled to EDIT_POLL_MIN_INTERVAL.
        """
        if self._suppressed:
            return
        now = time.time() if now is None else now
        if (now - self._last_poll_time) < EDIT_POLL_MIN_INTERVAL:
            return
        self._last_poll_time = now
        stack = self._operator_stack()
        count = len(stack)

        # First poll only establishes a baseline.
        if not self._seen_baseline:
            self._last_operator_count = count
            self._seen_baseline = True
            return

        if count <= self._last_operator_count:
            # Unchanged, or shrank because of an undo. Hold the high-water
            # mark so a later redo does not replay emitted operators.
            return

        for op in stack[self._last_operator_count:count]:
            self._record_operator(op)
        self._last_operator_count = count

    def _record_operator(self, op):
        try:
            bl_idname = getattr(op, "bl_idname", None)
            if not bl_idname:
                return
            # bl_idname is UPPER_CASE_OT_form; normalise to bpy.ops form.
            normalized = bl_idname.lower().replace("_ot_", ".", 1)
            if normalized in _IGNORED_OPERATORS:
                return
            self._events.append({
                "kind": "operator",
                "bl_idname": normalized,
                "name": getattr(op, "name", None),
                "properties": self._operator_properties(op),
                "timestamp": time.time(),
            })
        except Exception as e:
            print(f"Manual edit capture: failed to record operator: {e}")

    @staticmethod
    def _operator_properties(op):
        """Best-effort scalar snapshot of an operator's resolved properties."""
        props = {}
        try:
            rna_props = op.properties.bl_rna.properties
        except Exception:
            return props
        for prop in rna_props:
            if prop.identifier == "rna_type":
                continue
            if _is_path_property(prop.identifier):
                continue
            try:
                value = getattr(op.properties, prop.identifier)
            except Exception:
                continue
            if isinstance(value, str):
                props[prop.identifier] = value[:MAX_OPERATOR_PROPERTY_CHARS]
            elif isinstance(value, (bool, int, float)):
                props[prop.identifier] = value
            elif hasattr(value, "__len__") and not isinstance(value, (dict, bytes)):
                try:
                    items = [
                        v[:MAX_OPERATOR_PROPERTY_CHARS] if isinstance(v, str) else v
                        for v in value
                        if isinstance(v, (bool, int, float, str))
                    ]
                    if items and len(items) <= 16:
                        props[prop.identifier] = items
                except Exception:
                    continue
        return props

    def record_undo(self, kind):
        """Record an undo/redo. This is the strongest rejection signal we get."""
        if self._suppressed:
            return
        self._events.append({
            "kind": kind,
            "timestamp": time.time(),
        })
        # Keep the high-water mark so a redo does not re-emit consumed entries.
        self._last_operator_count = max(
            self._last_operator_count, len(self._operator_stack())
        )
        self._seen_baseline = True

    def drain(self):
        """Hand buffered events to the MCP server and clear them."""
        events = list(self._events)
        self._events.clear()
        return events


_edit_recorder = UserEditRecorder()


def get_edit_recorder():
    return _edit_recorder


@persistent
def _blendermcp_undo_post(scene, depsgraph=None):
    _edit_recorder.record_undo("undo")


@persistent
def _blendermcp_redo_post(scene, depsgraph=None):
    _edit_recorder.record_undo("redo")


@persistent
def _blendermcp_depsgraph_post(scene, depsgraph=None):
    _edit_recorder.poll_operators()


def _telemetry_consent_enabled():
    """Read the consent preference directly. Fails closed."""
    try:
        addon_prefs = bpy.context.preferences.addons.get(__name__)
        if not addon_prefs:
            return False
        return bool(addon_prefs.preferences.telemetry_consent)
    except Exception:
        return False


def _register_edit_capture_handlers():
    """Attach manual-edit handlers, but only with telemetry consent."""
    if not _telemetry_consent_enabled():
        _unregister_edit_capture_handlers()
        return False

    handlers = [
        (bpy.app.handlers.undo_post, _blendermcp_undo_post),
        (bpy.app.handlers.redo_post, _blendermcp_redo_post),
        (bpy.app.handlers.depsgraph_update_post, _blendermcp_depsgraph_post),
    ]
    for handler_list, fn in handlers:
        if fn not in handler_list:
            handler_list.append(fn)
    return True


def sync_edit_capture_handlers():
    """Re-apply the consent gate. Safe to call when consent or server state changes."""
    try:
        server_running = bool(
            getattr(bpy.types, "blendermcp_server", None)
            and bpy.types.blendermcp_server.running
        )
    except Exception:
        server_running = False

    if not server_running:
        _unregister_edit_capture_handlers()
        return False
    return _register_edit_capture_handlers()


def _unregister_edit_capture_handlers():
    handlers = [
        (bpy.app.handlers.undo_post, _blendermcp_undo_post),
        (bpy.app.handlers.redo_post, _blendermcp_redo_post),
        (bpy.app.handlers.depsgraph_update_post, _blendermcp_depsgraph_post),
    ]
    for handler_list, fn in handlers:
        with suppress(ValueError):
            handler_list.remove(fn)
#endregion


def get_blendermcp_addon_preferences(context=None):
    """Get add-on preferences object if available."""
    if context is None:
        context = bpy.context
    addon = context.preferences.addons.get(__name__)
    return addon.preferences if addon else None

class BlenderMCPServer:
    def __init__(self, host='localhost', port=9876):
        self.host = host
        self.port = port
        self.running = False
        self.socket = None
        self.server_thread = None
        # Commands are pushed here by client threads and drained by a single
        # timer running on Blender's main thread. bpy.app.timers is not
        # thread-safe, so registering a timer per command (the previous
        # approach) could silently drop the callback - on Windows especially -
        # leaving the client blocked in recv() until its socket timeout.
        self.command_queue = queue.Queue()
        # Live client sockets, so stop() can unblock threads parked in recv().
        self._clients = set()
        self._clients_lock = threading.Lock()

    def start(self):
        if bpy.app.background:
            print("BlenderMCP: cannot start server in background mode (blender -b) - commands would never execute\n"
                  "BlenderMCP: run Blender with a GUI, or use a virtual display: xvfb-run -a blender")
            return

        if self.running:
            print("Server is already running")
            return

        self.running = True

        try:
            # Create socket
            self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.socket.bind((self.host, self.port))
            # Backlog of 1 meant a reconnecting client could complete the TCP
            # handshake and then never be accept()ed - a connection that looks
            # established but is never serviced.
            self.socket.listen(5)

            # Start server thread
            self.server_thread = threading.Thread(target=self._server_loop)
            self.server_thread.daemon = True
            self.server_thread.start()

            _register_edit_capture_handlers()

            # start() is called from the operator, i.e. the main thread, so
            # this is the only safe place to touch bpy.app.timers.
            if not bpy.app.timers.is_registered(self._drain_command_queue):
                bpy.app.timers.register(self._drain_command_queue, persistent=True)

            print(f"BlenderMCP server started on {self.host}:{self.port}")
        except Exception as e:
            print(f"Failed to start server: {str(e)}")
            self.stop()

    def stop(self):
        self.running = False

        _unregister_edit_capture_handlers()
        get_edit_recorder().drain()

        try:
            if bpy.app.timers.is_registered(self._drain_command_queue):
                bpy.app.timers.unregister(self._drain_command_queue)
        except Exception:
            pass

        # Close socket
        if self.socket:
            try:
                self.socket.close()
            except:
                pass
            self.socket = None

        # Shut down live client sockets. Without this, handler threads stay
        # parked in a blocking recv() forever; being daemon threads they then
        # outlive the restart and close connections the new server owns
        # (the WinError 10054 seen after toggling the addon).
        with self._clients_lock:
            clients = list(self._clients)
            self._clients.clear()
        for client in clients:
            try:
                client.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass
            try:
                client.close()
            except Exception:
                pass

        # Drop any commands that will never be serviced now.
        while True:
            try:
                self.command_queue.get_nowait()
            except queue.Empty:
                break

        # Wait for thread to finish
        if self.server_thread:
            try:
                if self.server_thread.is_alive():
                    self.server_thread.join(timeout=1.0)
            except:
                pass
            self.server_thread = None

        print("BlenderMCP server stopped")

    def _server_loop(self):
        """Main server loop in a separate thread"""
        print("Server thread started")
        self.socket.settimeout(1.0)  # Timeout to allow for stopping

        while self.running:
            try:
                # Accept new connection
                try:
                    client, address = self.socket.accept()
                    print(f"Connected to client: {address}")

                    # Handle client in a separate thread
                    client_thread = threading.Thread(
                        target=self._handle_client,
                        args=(client,)
                    )
                    client_thread.daemon = True
                    client_thread.start()
                except socket.timeout:
                    # Just check running condition
                    continue
                except Exception as e:
                    print(f"Error accepting connection: {str(e)}")
                    time.sleep(0.5)
            except Exception as e:
                print(f"Error in server loop: {str(e)}")
                if not self.running:
                    break
                time.sleep(0.5)

        print("Server thread stopped")

    def _drain_command_queue(self):
        """Run queued commands on Blender's main thread.

        Registered once by start(); returns the poll interval so Blender keeps
        calling it. All bpy access happens here, on the main thread.
        """
        if not self.running:
            return None

        while True:
            try:
                command, client = self.command_queue.get_nowait()
            except queue.Empty:
                break

            try:
                response = self.execute_command(command)
                response_json = json.dumps(response)
            except Exception as e:
                print(f"Error executing command: {str(e)}")
                traceback.print_exc()
                response_json = json.dumps({"status": "error", "message": str(e)})

            try:
                client.sendall(response_json.encode('utf-8'))
            except Exception:
                print("Failed to send response - client disconnected")

        return 0.05

    def _handle_client(self, client):
        """Handle connected client"""
        print("Client handler started")
        # A finite timeout keeps this loop responsive to self.running instead
        # of parking in recv() forever.
        client.settimeout(1.0)
        with self._clients_lock:
            self._clients.add(client)
        buffer = b''

        try:
            while self.running:
                # Receive data
                try:
                    data = client.recv(8192)
                    if not data:
                        print("Client disconnected")
                        break

                    buffer += data
                    try:
                        # Try to parse command
                        command = json.loads(buffer.decode('utf-8'))
                        buffer = b''

                        # Hand off to the main thread. Never call
                        # bpy.app.timers.register() from here - it is not
                        # thread-safe and the callback can be silently lost.
                        print(f"Queued command: {command.get('type')}")
                        self.command_queue.put((command, client))
                    except (json.JSONDecodeError, UnicodeDecodeError):
                        # Incomplete data, wait for more. A multi-byte UTF-8
                        # character can land split across a recv() chunk
                        # boundary, which fails decode() before json.loads()
                        # ever runs - that's incomplete data too, not garbage.
                        pass
                except socket.timeout:
                    # Expected; loop round and re-check self.running.
                    continue
                except Exception as e:
                    print(f"Error receiving data: {str(e)}")
                    break
        except Exception as e:
            print(f"Error in client handler: {str(e)}")
        finally:
            with self._clients_lock:
                self._clients.discard(client)
            try:
                client.close()
            except:
                pass
            print("Client handler stopped")

    def execute_command(self, command):
        """Execute a command in the main Blender thread"""
        try:
            with get_edit_recorder().agent_command():
                return self._execute_command_internal(command)

        except Exception as e:
            print(f"Error executing command: {str(e)}")
            traceback.print_exc()
            return {"status": "error", "message": str(e)}

    def _execute_command_internal(self, command):
        """Internal command execution with proper context"""
        cmd_type = command.get("type")
        params = command.get("params", {})

        # Trivial liveness check. Touches no bpy data, so a successful ping
        # alongside a failing command isolates data access from transport.
        if cmd_type == "ping":
            return {"status": "success", "result": {"pong": True}}

        # Base handlers that are always available
        handlers = {
            "get_scene_info": self.get_scene_info,
            "get_world_state_snapshot": self.get_world_state_snapshot,
            "get_addon_info": self.get_addon_info,
            "get_object_info": self.get_object_info,
            "get_viewport_screenshot": self.get_viewport_screenshot,
            "execute_code": self.execute_code,
            "drain_human_activity": self.drain_human_activity,
            "get_telemetry_consent": self.get_telemetry_consent,
            "set_telemetry_consent": self.set_telemetry_consent,
        }

        handler = handlers.get(cmd_type)
        if handler:
            try:
                print(f"Executing handler for {cmd_type}")
                result = handler(**params)
                print(f"Handler execution complete")
                return {"status": "success", "result": result}
            except Exception as e:
                print(f"Error in handler: {str(e)}")
                traceback.print_exc()
                return {"status": "error", "message": str(e)}
        else:
            return {"status": "error", "message": f"Unknown command type: {cmd_type}"}



    def get_addon_info(self):
        """Version/capability handshake for the MCP server (and install tooling)."""
        return {
            "name": bl_info.get("name", "Blender MCP"),
            "addon_version": list(bl_info.get("version", (0, 0))),
            "protocol_version": ADDON_PROTOCOL_VERSION,
            "capabilities": sorted([
                "get_scene_info",
                "get_world_state_snapshot",
                "get_addon_info",
                "get_object_info",
                "get_viewport_screenshot",
                "execute_code",
                "drain_human_activity",
                "get_telemetry_consent",
                "set_telemetry_consent",
            ]),
            "blender_version": bpy.app.version_string,
        }

    def get_telemetry_consent(self):
        """Get the current telemetry consent status.

        Fails closed: if preferences cannot be read we report no consent. Not
        being able to read the preference means we do not know the user's
        answer, which is not the same as them having said yes.
        """
        try:
            addon_prefs = bpy.context.preferences.addons.get(__name__)
            if addon_prefs:
                consent = bool(addon_prefs.preferences.telemetry_consent)
            else:
                consent = False
        except (AttributeError, KeyError):
            consent = False
        return {"consent": consent}

    def set_telemetry_consent(self, consent=False):
        """Write the telemetry consent preference.

        Only reached when the user answered an elicitation prompt in their MCP
        client, or asked to opt out. Assigning the property in code skips the
        BoolProperty update= callback, so the manual-edit handlers are
        re-synced explicitly.
        """
        try:
            addon_prefs = bpy.context.preferences.addons.get(__name__)
            if not addon_prefs:
                return {"error": "Could not read addon preferences"}
            addon_prefs.preferences.telemetry_consent = bool(consent)
        except (AttributeError, KeyError) as e:
            return {"error": f"Could not set telemetry consent: {e}"}

        try:
            sync_edit_capture_handlers()
        except Exception as e:
            print(f"BlenderMCP: could not sync manual edit handlers: {e}")

        return {"consent": bool(consent)}

    def get_scene_info(self):
        """Get information about the current Blender scene"""
        try:
            print("Getting scene info...")
            # Simplify the scene info to reduce data size
            scene_info = {
                "name": bpy.context.scene.name,
                "object_count": len(bpy.context.scene.objects),
                "objects": [],
                "materials_count": len(bpy.data.materials),
            }

            # Collect minimal object information (limit to first 10 objects)
            for i, obj in enumerate(bpy.context.scene.objects):
                if i >= 10:  # Reduced from 20 to 10
                    break

                obj_info = {
                    "name": obj.name,
                    "type": obj.type,
                    # Only include basic location data
                    "location": [round(float(obj.location.x), 2),
                                round(float(obj.location.y), 2),
                                round(float(obj.location.z), 2)],
                }
                scene_info["objects"].append(obj_info)

            print(f"Scene info collected: {len(scene_info['objects'])} objects")
            return scene_info
        except Exception as e:
            print(f"Error in get_scene_info: {str(e)}")
            traceback.print_exc()
            return {"error": str(e)}

    def drain_human_activity(self):
        """Return human-originated events buffered since the last drain.

        Consent is enforced MCP-side (the server only drains and uploads when
        the user has opted in), but we also refuse here so a buffer does not
        accumulate for a user who has said no.
        """
        try:
            if not self.get_telemetry_consent().get("consent"):
                get_edit_recorder().drain()
                return {"events": []}
            return {"events": get_edit_recorder().drain()}
        except Exception as e:
            print(f"Error draining manual edits: {str(e)}")
            return {"error": str(e)}

    @staticmethod
    def _snapshot_geometry(obj):
        """World-space AABB + dimensions for one object, or None.

        Without these, downstream analysis cannot compute contact, containment
        or collision: `scale` alone is a multiplier on unknown base geometry.
        Uses obj.bound_box (8 cached local corners) rather than mesh vertices,
        so cost is constant per object regardless of poly count.
        """
        bound_box = getattr(obj, "bound_box", None)
        if not bound_box:
            return None
        try:
            matrix_world = obj.matrix_world
            xs, ys, zs = [], [], []
            for corner in bound_box:
                world = matrix_world @ mathutils.Vector(corner)
                xs.append(world.x)
                ys.append(world.y)
                zs.append(world.z)
            return {
                "aabb_min": [round(min(xs), 3), round(min(ys), 3), round(min(zs), 3)],
                "aabb_max": [round(max(xs), 3), round(max(ys), 3), round(max(zs), 3)],
                "dimensions": [
                    round(float(obj.dimensions.x), 3),
                    round(float(obj.dimensions.y), 3),
                    round(float(obj.dimensions.z), 3),
                ],
            }
        except Exception:
            return None

    @staticmethod
    def _snapshot_relations(obj):
        """Parent and constraint targets, so hierarchies read correctly.

        World `location` alone misreports parented objects, whose authored
        values are parent-relative.
        """
        relations = {}
        parent = getattr(obj, "parent", None)
        if parent:
            relations["parent"] = parent.name
            relations["parent_type"] = obj.parent_type
            loc = obj.matrix_local.translation
            relations["local_location"] = [
                round(float(loc.x), 3),
                round(float(loc.y), 3),
                round(float(loc.z), 3),
            ]
        constraints = []
        for constraint in getattr(obj, "constraints", None) or []:
            entry = {"type": constraint.type}
            target = getattr(constraint, "target", None)
            if target:
                entry["target"] = target.name
            constraints.append(entry)
            if len(constraints) >= 8:
                break
        if constraints:
            relations["constraints"] = constraints
        modifiers = [m.type for m in (getattr(obj, "modifiers", None) or [])[:8]]
        if modifiers:
            relations["modifiers"] = modifiers
        return relations

    @staticmethod
    def _snapshot_animation(obj):
        """Action name and per-channel keyframe summary for one object, or {}.

        Static transforms alone cannot distinguish an authored edit from
        playback landing on a different frame. Reads F-curve metadata
        (`data_path`, `array_index`, `len(keyframe_points)`) rather than
        individual keyframes, so cost stays proportional to channel count
        rather than to animation length.
        """
        try:
            anim_data = getattr(obj, "animation_data", None)
            if not anim_data:
                return {}

            animation = {}
            action = getattr(anim_data, "action", None)
            if action:
                animation["action"] = action.name
                channels = []
                total_keyframes = 0
                frame_min, frame_max = None, None
                for fcurve in action.fcurves:
                    keyframe_points = fcurve.keyframe_points
                    count = len(keyframe_points)
                    total_keyframes += count
                    if count and len(channels) < 16:
                        channels.append({
                            "data_path": fcurve.data_path,
                            "array_index": fcurve.array_index,
                            "keyframes": count,
                        })
                    if count:
                        first = keyframe_points[0].co.x
                        last = keyframe_points[-1].co.x
                        frame_min = first if frame_min is None else min(frame_min, first)
                        frame_max = last if frame_max is None else max(frame_max, last)
                if channels:
                    animation["channels"] = channels
                animation["keyframe_count"] = total_keyframes
                if frame_min is not None:
                    animation["frame_range"] = [round(float(frame_min), 3),
                                                round(float(frame_max), 3)]

            drivers = getattr(anim_data, "drivers", None)
            if drivers and len(drivers):
                animation["driver_count"] = len(drivers)

            nla_tracks = [
                track.name
                for track in (getattr(anim_data, "nla_tracks", None) or [])[:8]
            ]
            if nla_tracks:
                animation["nla_tracks"] = nla_tracks

            return {"animation": animation} if animation else {}
        except Exception:
            return {}

    @staticmethod
    def _shader_fingerprint(id_block):
        """Stable short hash of a node tree (material or world), or None.

        Node identities plus rounded input values, so tweaking a color or
        rewiring a link changes the fingerprint. Lets downstream deltas see
        shader edits that leave every object transform untouched.
        """
        try:
            if id_block is None:
                return None
            tree = id_block.node_tree if getattr(id_block, "use_nodes", False) else None
            if tree is None:
                color = getattr(id_block, "diffuse_color", None) or getattr(id_block, "color", None)
                basis = str([round(float(v), 3) for v in color]) if color is not None else ""
            else:
                parts = []
                for node in tree.nodes:
                    values = []
                    for sock in node.inputs:
                        dv = getattr(sock, "default_value", None)
                        if isinstance(dv, (int, float)):
                            values.append(round(float(dv), 3))
                        elif dv is not None:
                            with suppress(TypeError, ValueError):
                                values.extend(round(float(v), 3) for v in dv)
                    parts.append(f"{node.bl_idname}{values}")
                parts.sort()
                parts.append(str(len(tree.links)))
                basis = "|".join(parts)
            return format(zlib.crc32(basis.encode("utf-8")), "08x")
        except Exception:
            return None

    @staticmethod
    def _project_id():
        """Salted hash linking sessions on the same .blend without storing its path."""
        try:
            filepath = bpy.data.filepath
            if not filepath:
                return None
            return hashlib.sha256(f"{uuid.getnode()}:{filepath}".encode("utf-8")).hexdigest()[:16]
        except Exception:
            return None

    def get_world_state_snapshot(self):
        """Compact world-state snapshot for trajectory capture (no mesh/shader detail)."""
        try:
            scene = bpy.context.scene
            selected = [obj.name for obj in bpy.context.selected_objects]
            selected_count = len(selected)
            selected_truncated = selected_count > MAX_SNAPSHOT_SELECTED
            if selected_truncated:
                # Sorted so before/after snapshots keep the same subset.
                selected = sorted(selected)[:MAX_SNAPSHOT_SELECTED]
            objects = []

            all_objects = list(scene.objects)
            truncated = len(all_objects) > MAX_SNAPSHOT_OBJECTS
            if truncated:
                # scene.objects iterates in an order that shifts as objects are
                # created, so an arbitrary prefix would leave the before/after
                # snapshots of one step holding different subsets and the delta
                # reporting phantom adds/removes. Sorting keeps them aligned.
                all_objects = sorted(all_objects, key=lambda o: o.name)[:MAX_SNAPSHOT_OBJECTS]

            for obj in all_objects:
                materials = []
                if getattr(obj, "material_slots", None):
                    materials = [
                        slot.material.name
                        for slot in obj.material_slots
                        if slot.material
                    ]

                entry = {
                    "name": obj.name,
                    "type": obj.type,
                    "location": [
                        round(float(obj.location.x), 3),
                        round(float(obj.location.y), 3),
                        round(float(obj.location.z), 3),
                    ],
                    "rotation": [
                        round(float(obj.rotation_euler.x), 3),
                        round(float(obj.rotation_euler.y), 3),
                        round(float(obj.rotation_euler.z), 3),
                    ],
                    "scale": [
                        round(float(obj.scale.x), 3),
                        round(float(obj.scale.y), 3),
                        round(float(obj.scale.z), 3),
                    ],
                    "visible": bool(obj.visible_get()),
                    "materials": materials,
                }
                geometry = self._snapshot_geometry(obj)
                if geometry:
                    entry.update(geometry)
                entry.update(self._snapshot_relations(obj))
                entry.update(self._snapshot_animation(obj))
                data = getattr(obj, "data", None)
                if obj.type == "MESH" and data is not None:
                    entry["mesh"] = {
                        "vertices": len(data.vertices),
                        "polygons": len(data.polygons),
                    }
                objects.append(entry)

            camera = scene.camera
            camera_info = None
            if camera:
                camera_info = {
                    "name": camera.name,
                    "location": [
                        round(float(camera.location.x), 3),
                        round(float(camera.location.y), 3),
                        round(float(camera.location.z), 3),
                    ],
                    "rotation": [
                        round(float(camera.rotation_euler.x), 3),
                        round(float(camera.rotation_euler.y), 3),
                        round(float(camera.rotation_euler.z), 3),
                    ],
                }
                if camera.type == "CAMERA" and camera.data:
                    camera_info["lens"] = round(float(camera.data.lens), 3)
                    camera_info["sensor_width"] = round(float(camera.data.sensor_width), 3)

            lights = []
            for obj in scene.objects:
                if obj.type != "LIGHT":
                    continue
                light_entry = {
                    "name": obj.name,
                    "location": [
                        round(float(obj.location.x), 3),
                        round(float(obj.location.y), 3),
                        round(float(obj.location.z), 3),
                    ],
                }
                if obj.data:
                    light_entry["light_type"] = obj.data.type
                    light_entry["energy"] = round(float(obj.data.energy), 3)
                lights.append(light_entry)
                if len(lights) >= 20:
                    break

            return {
                "name": scene.name,
                "object_count": len(scene.objects),
                # Explicit, so consumers never have to infer truncation from a
                # hardcoded cap they might disagree with.
                "objects_listed": len(objects),
                "objects_truncated": truncated,
                "selected": selected,
                "selected_count": selected_count,
                "selected_truncated": selected_truncated,
                "frame_current": scene.frame_current,
                "frame_start": scene.frame_start,
                "frame_end": scene.frame_end,
                "fps": round(float(scene.render.fps) / scene.render.fps_base, 3),
                "objects": objects,
                "active_camera": camera.name if camera else None,
                "camera": camera_info,
                "lights": lights,
                "materials_count": len(bpy.data.materials),
                "material_fps": {
                    m.name: self._shader_fingerprint(m)
                    for m in list(bpy.data.materials)[:200]
                },
                "world_fp": self._shader_fingerprint(scene.world),
                "project_id": self._project_id(),
                "blender_version": bpy.app.version_string,
                "snapshot_source": "native",
            }
        except Exception as e:
            print(f"Error in get_world_state_snapshot: {str(e)}")
            traceback.print_exc()
            return {"error": str(e)}

    @staticmethod
    def _get_aabb(obj):
        """ Returns the world-space axis-aligned bounding box (AABB) of an object. """
        if obj.type != 'MESH':
            raise TypeError("Object must be a mesh")

        # Get the bounding box corners in local space
        local_bbox_corners = [mathutils.Vector(corner) for corner in obj.bound_box]

        # Convert to world coordinates
        world_bbox_corners = [obj.matrix_world @ corner for corner in local_bbox_corners]

        # Compute axis-aligned min/max coordinates
        min_corner = mathutils.Vector(map(min, zip(*world_bbox_corners)))
        max_corner = mathutils.Vector(map(max, zip(*world_bbox_corners)))

        return [
            [*min_corner], [*max_corner]
        ]

    def get_object_info(self, name):
        """Get detailed information about a specific object"""
        obj = bpy.data.objects.get(name)
        if not obj:
            raise ValueError(f"Object not found: {name}")

        # Basic object info
        obj_info = {
            "name": obj.name,
            "type": obj.type,
            "location": [obj.location.x, obj.location.y, obj.location.z],
            "rotation": [obj.rotation_euler.x, obj.rotation_euler.y, obj.rotation_euler.z],
            "scale": [obj.scale.x, obj.scale.y, obj.scale.z],
            "visible": obj.visible_get(),
            "materials": [],
        }

        if obj.type == "MESH":
            bounding_box = self._get_aabb(obj)
            obj_info["world_bounding_box"] = bounding_box

        # Add material slots
        for slot in obj.material_slots:
            if slot.material:
                obj_info["materials"].append(slot.material.name)

        # Add mesh data if applicable
        if obj.type == 'MESH' and obj.data:
            mesh = obj.data
            obj_info["mesh"] = {
                "vertices": len(mesh.vertices),
                "edges": len(mesh.edges),
                "polygons": len(mesh.polygons),
            }

        return obj_info

    def get_viewport_screenshot(self, max_size=800, filepath=None, format="png"):
        """
        Capture a screenshot of the current 3D viewport and save it to the specified path.

        Parameters:
        - max_size: Maximum size in pixels for the largest dimension of the image
        - filepath: Path where to save the screenshot file
        - format: Image format (png, jpg, etc.)

        Returns success/error status
        """
        # screen.screenshot_area captures the OS window framebuffer, which is
        # all-black whenever the Blender window is not composited in the
        # foreground (the normal case when Blender is driven headless-style via
        # MCP). Render the viewport with gpu.types.GPUOffScreen.draw_view3d
        # instead, which is independent of window compositing state, and fall
        # back to the window grab if offscreen rendering is unavailable (e.g. no
        # GPU context). The response reports which path produced the image.
        try:
            if not filepath:
                return {"error": "No filepath provided"}

            area = region = space = None
            for a in bpy.context.screen.areas:
                if a.type == 'VIEW_3D':
                    area = a
                    space = a.spaces.active
                    region = next((r for r in a.regions if r.type == 'WINDOW'), None)
                    break

            if not area or region is None or space is None:
                return {"error": "No 3D viewport found"}

            method = "offscreen"
            try:
                import gpu
                import numpy as np

                r3d = space.region_3d
                src_w, src_h = region.width, region.height
                if max(src_w, src_h) > max_size:
                    s = max_size / max(src_w, src_h)
                    width, height = max(1, int(src_w * s)), max(1, int(src_h * s))
                else:
                    width, height = src_w, src_h

                offscreen = gpu.types.GPUOffScreen(width, height)
                try:
                    offscreen.draw_view3d(
                        bpy.context.scene, bpy.context.view_layer, space, region,
                        r3d.view_matrix, r3d.window_matrix, do_color_management=True,
                    )
                    buf = offscreen.texture_color.read()
                finally:
                    offscreen.free()

                buf.dimensions = width * height * 4
                pixels = np.asarray(buf, dtype=np.float32) / 255.0  # GPU buffer is 0..255

                image = bpy.data.images.new("mcp_viewport", width, height, alpha=True)
                image.pixels.foreach_set(pixels.ravel())
                image.filepath_raw = filepath
                image.file_format = format.upper()
                image.save()
                bpy.data.images.remove(image)

            except Exception as offscreen_err:
                print(f"[BlenderMCP] offscreen capture failed ({offscreen_err}); "
                      "falling back to window grab", flush=True)
                method = "window_grab"
                with bpy.context.temp_override(area=area):
                    bpy.ops.screen.screenshot_area(filepath=filepath)
                img = bpy.data.images.load(filepath)
                width, height = img.size
                if max(width, height) > max_size:
                    s = max_size / max(width, height)
                    width, height = int(width * s), int(height * s)
                    img.scale(width, height)
                    img.file_format = format.upper()
                    img.save()
                bpy.data.images.remove(img)

            return {
                "success": True,
                "width": width,
                "height": height,
                "filepath": filepath,
                "method": method,
            }

        except Exception as e:
            return {"error": str(e)}

    def execute_code(self, code):
        """Execute arbitrary Blender Python code"""
        # This is powerful but potentially dangerous - use with caution
        try:
            # Create a local namespace for execution
            namespace = {"bpy": bpy}

            # Capture stdout during execution, and return it as result
            capture_buffer = io.StringIO()
            with redirect_stdout(capture_buffer):
                exec(code, namespace)

            captured_output = capture_buffer.getvalue()
            return {"executed": True, "result": captured_output}
        except Exception as e:
            raise Exception(f"Code execution error: {str(e)}")



# Blender Addon Preferences
class BLENDERMCP_AddonPreferences(bpy.types.AddonPreferences):
    bl_idname = __name__
    
    def _on_telemetry_consent_changed(self, context):
        try:
            sync_edit_capture_handlers()
        except Exception as e:
            print(f"BlenderMCP: could not sync manual edit handlers: {e}")

    telemetry_consent: BoolProperty(
        name="Allow Telemetry",
        description="Allow collection of prompts, code snippets, screenshots, and trajectory data to help improve Blender MCP",
        default=True,
        update=_on_telemetry_consent_changed,
    )

    def draw(self, context):
        layout = self.layout
        
        # Telemetry section
        layout.label(text="Telemetry & Privacy:", icon='PREFERENCES')
        
        box = layout.box()
        row = box.row()
        row.prop(self, "telemetry_consent", text="Allow Telemetry")

        # Info text
        box.separator()
        if self.telemetry_consent:
            box.label(text="With consent: We collect anonymized prompts, code, screenshots,", icon='INFO')
            box.label(text="and trajectory data (actions, scene state, feedback).", icon='BLANK1')
        else:
            box.label(text="Without consent: We only collect minimal anonymous usage data", icon='INFO')
            box.label(text="(tool names, success/failure, duration - no prompts or code).", icon='BLANK1')
        box.separator()
        box.label(text="Data is not linked to your name or account. Change this anytime.", icon='CHECKMARK')
        
        # Terms and Conditions link
        box.separator()
        row = box.row()
        row.operator("blendermcp.open_terms", text="View Terms and Conditions", icon='TEXT')

# Blender UI Panel
class BLENDERMCP_PT_Panel(bpy.types.Panel):
    bl_label = "Blender MCP"
    bl_idname = "BLENDERMCP_PT_Panel"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = 'BlenderMCP'

    def draw(self, context):
        layout = self.layout
        scene = context.scene

        layout.prop(scene, "blendermcp_port")

        if not scene.blendermcp_server_running:
            layout.operator("blendermcp.start_server", text="Connect to MCP server")
        else:
            layout.operator("blendermcp.stop_server", text="Disconnect from MCP server")
            layout.label(text=f"Running on port {scene.blendermcp_port}")
        
        # Feedback section
        layout.separator()
        feedback_box = layout.box()
        
        col = feedback_box.column(align=True)
        col.label(text="Feedback", icon='URL')
        col.label(text="bit.ly/blender-mcp-form")
        col.separator()
        col.label(text="Schedule a call", icon='URL')
        col.label(text="bit.ly/blender-mcp-call")
        col.label(text="(we'll credit you in the repo!)")

# Operator to start the server
class BLENDERMCP_OT_StartServer(bpy.types.Operator):
    bl_idname = "blendermcp.start_server"
    bl_label = "Connect to Claude"
    bl_description = "Start the BlenderMCP server to connect with Claude"

    def execute(self, context):
        scene = context.scene

        # Create a new server instance
        if not hasattr(bpy.types, "blendermcp_server") or not bpy.types.blendermcp_server:
            bpy.types.blendermcp_server = BlenderMCPServer(port=scene.blendermcp_port)

        # Start the server
        bpy.types.blendermcp_server.start()
        scene.blendermcp_server_running = bpy.types.blendermcp_server.running

        return {'FINISHED'}

# Operator to stop the server
class BLENDERMCP_OT_StopServer(bpy.types.Operator):
    bl_idname = "blendermcp.stop_server"
    bl_label = "Stop the connection to Claude"
    bl_description = "Stop the connection to Claude"

    def execute(self, context):
        scene = context.scene

        # Stop the server if it exists
        if hasattr(bpy.types, "blendermcp_server") and bpy.types.blendermcp_server:
            bpy.types.blendermcp_server.stop()
            del bpy.types.blendermcp_server

        scene.blendermcp_server_running = False

        return {'FINISHED'}

# Operator to open Terms and Conditions
class BLENDERMCP_OT_OpenTerms(bpy.types.Operator):
    bl_idname = "blendermcp.open_terms"
    bl_label = "View Terms and Conditions"
    bl_description = "Open the Terms and Conditions document"

    def execute(self, context):
        # Open the Terms and Conditions on GitHub
        terms_url = "https://github.com/ahujasid/blender-mcp/blob/main/TERMS_AND_CONDITIONS.md"
        try:
            import webbrowser
            webbrowser.open(terms_url)
            self.report({'INFO'}, "Terms and Conditions opened in browser")
        except Exception as e:
            self.report({'ERROR'}, f"Could not open Terms and Conditions: {str(e)}")
        
        return {'FINISHED'}

# Registration functions
def register():
    bpy.types.Scene.blendermcp_port = IntProperty(
        name="Port",
        description="Port for the BlenderMCP server",
        default=9876,
        min=1024,
        max=65535
    )

    bpy.types.Scene.blendermcp_server_running = bpy.props.BoolProperty(
        name="Server Running",
        default=False
    )

    bpy.types.Scene.blendermcp_auto_start_server = bpy.props.BoolProperty(
        name="Auto-Start Server",
        description="Automatically start the MCP server when Blender loads",
        default=True
    )

    # Register preferences class
    bpy.utils.register_class(BLENDERMCP_AddonPreferences)

    bpy.utils.register_class(BLENDERMCP_PT_Panel)
    bpy.utils.register_class(BLENDERMCP_OT_StartServer)
    bpy.utils.register_class(BLENDERMCP_OT_StopServer)
    bpy.utils.register_class(BLENDERMCP_OT_OpenTerms)

    # Auto-start the server so the MCP client can connect without manual UI interaction
    scene = getattr(bpy.context, 'scene', None)
    if scene is not None:
        port = scene.blendermcp_port
        auto_start = scene.blendermcp_auto_start_server
    else:
        port = 9876
        auto_start = True

    if auto_start and (not hasattr(bpy.types, "blendermcp_server") or not bpy.types.blendermcp_server):
        bpy.types.blendermcp_server = BlenderMCPServer(port=port)
    if auto_start and not bpy.types.blendermcp_server.running:
        bpy.types.blendermcp_server.start()
        try:
            bpy.context.scene.blendermcp_server_running = bpy.types.blendermcp_server.running
        except AttributeError:
            pass

    print("BlenderMCP addon registered")

def unregister():
    _unregister_edit_capture_handlers()

    # Stop the server if it's running
    if hasattr(bpy.types, "blendermcp_server") and bpy.types.blendermcp_server:
        bpy.types.blendermcp_server.stop()
        del bpy.types.blendermcp_server

    bpy.utils.unregister_class(BLENDERMCP_PT_Panel)
    bpy.utils.unregister_class(BLENDERMCP_OT_StartServer)
    bpy.utils.unregister_class(BLENDERMCP_OT_StopServer)
    bpy.utils.unregister_class(BLENDERMCP_OT_OpenTerms)
    bpy.utils.unregister_class(BLENDERMCP_AddonPreferences)

    del bpy.types.Scene.blendermcp_port
    del bpy.types.Scene.blendermcp_server_running
    del bpy.types.Scene.blendermcp_auto_start_server

    print("BlenderMCP addon unregistered")

if __name__ == "__main__":
    register()
