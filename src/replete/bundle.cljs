;; A namespace used to cause additional libs to be included in out for bundling.
(ns replete.bundle
  (:require
    chivorcam.core
    clojure.core.reducers
    clojure.data
    clojure.datafy
    clojure.edn
    clojure.reflect
    clojure.test.check
    clojure.test.check.clojure-test
    clojure.test.check.generators
    clojure.test.check.properties
    clojure.zip
    cljs.analyzer.api
    cljs.pprint
    cljs.spec.alpha
    cljs.spec.test.alpha
    cljs.spec.gen.alpha
    cljs.test
    cljs.core.async
    cljs.core.async.impl.ioc-macros-runtime
    goog.Disposable
    goog.History
    goog.History.Event
    goog.History.EventType
    goog.Promise
    goog.Thenable
    goog.Throttle
    goog.Timer
    goog.Uri
    goog.Uri.QueryData
    goog.a11y.aria
    goog.a11y.aria.Announcer
    goog.a11y.aria.AutoCompleteValues
    goog.a11y.aria.CheckedValues
    goog.a11y.aria.DropEffectValues
    goog.a11y.aria.ExpandedValues
    goog.a11y.aria.GrabbedValues
    goog.a11y.aria.InvalidValues
    goog.a11y.aria.LivePriority
    goog.a11y.aria.OrientationValues
    goog.a11y.aria.PressedValues
    goog.a11y.aria.RelevantValues
    goog.a11y.aria.Role
    goog.a11y.aria.SelectedValues
    goog.a11y.aria.SortValues
    goog.a11y.aria.State
    goog.a11y.aria.datatables
    goog.array
    goog.asserts
    goog.asserts.AssertionError
    goog.async.AnimationDelay
    goog.async.ConditionalDelay
    goog.async.Debouncer
    goog.async.Delay
    goog.async.FreeList
    goog.async.Throttle
    goog.async.WorkQueue
    goog.async.nextTick
    goog.async.run
    goog.async.throwException
    goog.color
    goog.color.Hsl
    goog.color.Hsv
    goog.color.Rgb
    goog.color.alpha
    goog.color.names
    goog.crypt
    goog.crypt.Aes
    goog.crypt.Arc4
    goog.crypt.BlobHasher
    goog.crypt.BlobHasher.EventType
    goog.crypt.BlockCipher
    goog.crypt.Cbc
    goog.crypt.Ctr
    goog.crypt.Hash
    goog.crypt.Hmac
    goog.crypt.Md5
    goog.crypt.Sha1
    goog.crypt.Sha2
    goog.crypt.Sha224
    goog.crypt.Sha256
    goog.crypt.Sha2_64bit
    goog.crypt.Sha384
    goog.crypt.Sha512
    goog.crypt.Sha512_256
    goog.crypt.base64
    goog.crypt.baseN
    goog.crypt.byteArrayToStringPerf
    goog.crypt.hash32
    goog.crypt.hashTester
    goog.crypt.pbkdf2
    goog.cssom
    goog.cssom.CssRuleType
    goog.cssom.iframe.style
    goog.date
    goog.date.Date
    goog.date.DateLike
    goog.date.DateRange
    goog.date.DateRange.Iterator
    goog.date.DateRange.StandardDateRangeKeys
    goog.date.DateTime
    goog.date.Interval
    goog.date.UtcDateTime
    goog.date.duration
    goog.date.month
    goog.date.relative
    goog.date.relative.TimeDeltaFormatter
    goog.date.relative.Unit
    goog.date.weekDay
    goog.disposable.IDisposable
    goog.dispose
    goog.disposeAll
    goog.format
    goog.format.EmailAddress
    goog.format.HtmlPrettyPrinter
    goog.format.HtmlPrettyPrinter.Buffer
    goog.format.InternationalizedEmailAddress
    goog.format.JsonPrettyPrinter
    goog.format.JsonPrettyPrinter.SafeHtmlDelimiters
    goog.format.JsonPrettyPrinter.TextDelimiters
    goog.fs
    goog.fs.DOMErrorLike
    goog.fs.DirectoryEntry
    goog.fs.DirectoryEntry.Behavior
    goog.fs.DirectoryEntryImpl
    goog.fs.Entry
    goog.fs.EntryImpl
    goog.fs.Error
    goog.fs.Error.ErrorCode
    goog.fs.FileEntry
    goog.fs.FileEntryImpl
    goog.fs.FileReader
    goog.fs.FileReader.EventType
    goog.fs.FileReader.ReadyState
    goog.fs.FileSaver
    goog.fs.FileSaver.EventType
    goog.fs.FileSaver.ReadyState
    goog.fs.FileSystem
    goog.fs.FileSystemImpl
    goog.fs.FileWriter
    goog.fs.ProgressEvent
    goog.fs.url
    goog.functions
    goog.history.Event
    goog.history.EventType
    goog.history.Html5History
    goog.history.Html5History.TokenTransformer
    goog.i18n.BidiFormatter
    goog.i18n.CharListDecompressor
    goog.i18n.CharPickerData
    goog.i18n.CompactNumberFormatSymbols
    goog.i18n.CompactNumberFormatSymbolsExt
    goog.i18n.DateTimeFormat
    goog.i18n.DateTimeFormat.Format
    goog.i18n.DateTimeParse
    goog.i18n.DateTimePatterns
    goog.i18n.DateTimePatternsExt
    goog.i18n.DateTimeSymbols
    goog.i18n.DateTimeSymbolsExt
    goog.i18n.DateTimeSymbolsType
    goog.i18n.GraphemeBreak
    goog.i18n.MessageFormat
    goog.i18n.NumberFormat
    goog.i18n.NumberFormat.CurrencyStyle
    goog.i18n.NumberFormat.Format
    goog.i18n.NumberFormatSymbols
    goog.i18n.NumberFormatSymbolsExt
    goog.i18n.TimeZone
    goog.i18n.bidi
    goog.i18n.bidi.Dir
    goog.i18n.bidi.DirectionalString
    goog.i18n.bidi.Format
    goog.i18n.collation
    goog.i18n.currency
    goog.i18n.currency.CurrencyInfo
    goog.i18n.currency.CurrencyInfoTier2
    goog.i18n.currencyCodeMap
    goog.i18n.currencyCodeMapTier2
    goog.i18n.mime
    goog.i18n.mime.encode
    goog.i18n.ordinalRules
    goog.i18n.pluralRules
    goog.i18n.uChar
    goog.i18n.uChar.LocalNameFetcher
    goog.i18n.uChar.NameFetcher
    goog.i18n.uChar.RemoteNameFetcher
    goog.i18n.uCharNames
    goog.iter
    goog.iter.Iterable
    goog.iter.Iterator
    goog.iter.StopIteration
    goog.json
    goog.json.NativeJsonProcessor
    goog.json.Processor
    goog.json.Replacer
    goog.json.Reviver
    goog.json.Serializer
    goog.json.hybrid
    goog.jsonPerf
    goog.log
    goog.log.Level
    goog.log.LogRecord
    goog.log.Logger
    goog.math
    goog.math.AffineTransform
    goog.math.Bezier
    goog.math.Box
    goog.math.Coordinate
    goog.math.Coordinate3
    goog.math.ExponentialBackoff
    goog.math.IRect
    goog.math.Integer
    goog.math.Line
    goog.math.Long
    goog.math.Matrix
    goog.math.Path
    goog.math.Path.Segment
    goog.math.Range
    goog.math.RangeSet
    goog.math.Rect
    goog.math.Size
    goog.math.Vec2
    goog.math.Vec3
    goog.math.interpolator.Interpolator1
    goog.math.interpolator.Linear1
    goog.math.interpolator.Pchip1
    goog.math.interpolator.Spline1
    goog.math.paths
    goog.math.tdma
    goog.memoize
    goog.object
    goog.positioning
    goog.positioning.AbsolutePosition
    goog.positioning.AbstractPosition
    goog.positioning.AnchoredPosition
    goog.positioning.AnchoredViewportPosition
    goog.positioning.ClientPosition
    goog.positioning.Corner
    goog.positioning.CornerBit
    goog.positioning.MenuAnchoredPosition
    goog.positioning.Overflow
    goog.positioning.OverflowStatus
    goog.positioning.ViewportClientPosition
    goog.positioning.ViewportPosition
    goog.promise.Resolver
    goog.promise.testSuiteAdapter
    goog.proto
    goog.proto.Serializer
    goog.proto2.Descriptor
    goog.proto2.FieldDescriptor
    goog.proto2.LazyDeserializer
    goog.proto2.Message
    goog.proto2.Metadata
    goog.proto2.ObjectSerializer
    goog.proto2.PbLiteSerializer
    goog.proto2.Serializer
    goog.proto2.TextFormatSerializer
    goog.proto2.Util
    goog.pubsub.PubSub
    goog.pubsub.TopicId
    goog.pubsub.TypedPubSub
    goog.reflect
    goog.spell.SpellCheck
    goog.spell.SpellCheck.WordChangedEvent
    goog.stats.BasicStat
    goog.storage.CollectableStorage
    goog.storage.EncryptedStorage
    goog.storage.ErrorCode
    goog.storage.ExpiringStorage
    goog.storage.RichStorage
    goog.storage.RichStorage.Wrapper
    goog.storage.Storage
    goog.storage.collectableStorageTester
    goog.storage.mechanism.ErrorCode
    goog.storage.mechanism.ErrorHandlingMechanism
    goog.storage.mechanism.HTML5LocalStorage
    goog.storage.mechanism.HTML5SessionStorage
    goog.storage.mechanism.HTML5WebStorage
    goog.storage.mechanism.IEUserData
    goog.storage.mechanism.IterableMechanism
    goog.storage.mechanism.Mechanism
    goog.storage.mechanism.PrefixedMechanism
    goog.storage.mechanism.iterableMechanismTester
    goog.storage.mechanism.mechanismSeparationTester
    goog.storage.mechanism.mechanismSharingTester
    goog.storage.mechanism.mechanismTestDefinition
    goog.storage.mechanism.mechanismTester
    goog.storage.mechanism.mechanismfactory
    goog.storage.storageTester
    goog.string
    goog.string.Const
    goog.string.Parser
    goog.string.StringBuffer
    goog.string.Stringifier
    goog.string.TypedString
    goog.string.Unicode
    goog.string.format
    goog.string.linkify
    goog.string.newlines
    goog.string.newlines.Line
    goog.string.path
    goog.structs
    goog.structs.CircularBuffer
    goog.structs.Collection
    goog.structs.Heap
    goog.structs.InversionMap
    goog.structs.LinkedMap
    goog.structs.Map
    goog.structs.Node
    goog.structs.Pool
    goog.structs.PriorityPool
    goog.structs.PriorityQueue
    goog.structs.QuadTree
    goog.structs.QuadTree.Node
    goog.structs.QuadTree.Point
    goog.structs.Queue
    goog.structs.Set
    goog.structs.SimplePool
    goog.structs.StringSet
    goog.structs.TreeNode
    goog.structs.Trie
    goog.style
    goog.style.bidi
    goog.style.cursor
    goog.style.transform
    goog.style.transition
    goog.style.transition.Css3Property
    goog.styleScrollbarTester
    goog.tweak
    goog.tweak.BaseEntry
    goog.tweak.BasePrimitiveSetting
    goog.tweak.BaseSetting
    goog.tweak.BooleanGroup
    goog.tweak.BooleanInGroupSetting
    goog.tweak.BooleanSetting
    goog.tweak.ButtonAction
    goog.tweak.ConfigParams
    goog.tweak.EntriesPanel
    goog.tweak.NumericSetting
    goog.tweak.Registry
    goog.tweak.StringSetting
    goog.tweak.TweakUi
    goog.tweak.testhelpers
    goog.uri.utils
    goog.uri.utils.ComponentIndex
    goog.uri.utils.QueryArray
    goog.uri.utils.QueryValue
    goog.uri.utils.StandardQueryParam
    goog.vec
    goog.vec.AnyType
    goog.vec.ArrayType
    goog.vec.Float32
    goog.vec.Float32Array
    goog.vec.Float64
    goog.vec.Float64Array
    goog.vec.Mat3
    goog.vec.Mat4
    goog.vec.Number
    goog.vec.Quaternion
    goog.vec.Quaternion.AnyType
    goog.vec.Ray
    goog.vec.Vec2
    goog.vec.Vec3
    goog.vec.Vec4
    goog.vec.mat3d
    goog.vec.mat3d.Type
    goog.vec.mat3f
    goog.vec.mat3f.Type
    goog.vec.mat4d
    goog.vec.mat4d.Type
    goog.vec.mat4f
    goog.vec.mat4f.Type
    goog.vec.vec2d
    goog.vec.vec2d.Type
    goog.vec.vec2f
    goog.vec.vec2f.Type
    goog.vec.vec3d
    goog.vec.vec3d.Type
    goog.vec.vec3f
    goog.vec.vec3f.Type
    goog.vec.vec4d
    goog.vec.vec4d.Type
    goog.vec.vec4f
    goog.vec.vec4f.Type
    goog.webgl
    goog.window
    goog.async.Deferred
    goog.async.Deferred.AlreadyCalledError
    goog.async.Deferred.CanceledError
    goog.async.DeferredList))
