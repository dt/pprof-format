/**
 * Unless explicitly stated otherwise all files in this repository are licensed under the MIT License.
 *
 * This product includes software developed at Datadog (https://www.datadoghq.com/  Copyright 2022 Datadog, Inc.
 */

/*!
 * Private helpers. These are only used by other helpers.
 */
const lowMaxBig = 2n ** 32n - 1n
const lowMax = 2 ** 32 - 1
const lowMaxPlus1 = lowMax + 1

// Buffer.from(string, 'utf8') is faster, when available
const toUtf8 = typeof Buffer === 'undefined'
  ? (value: string) => new TextEncoder().encode(value)
  : (value: string) => Buffer.from(value, 'utf8')

type Numeric = number | bigint

type DeepPartial<T> = {
  [P in keyof T]?: DeepPartial<T[P]>
}

function countNumberBytes(buffer: Uint8Array, start = 0): number {
  if (start >= buffer.length) return 0

  // Fast path for single-byte numbers (most common case)
  if (buffer[start] < 0b10000000) return 1

  let i = start
  while (i < buffer.length && buffer[i++] >= 0b10000000);
  return i - start
}

function decodeBigNumber(buffer: Uint8Array): bigint {
  if (!buffer.length) return BigInt(0)
  let value = BigInt(buffer[0] & 0b01111111)
  let i = 0
  while (buffer[i++] >= 0b10000000) {
    value |= BigInt(buffer[i] & 0b01111111) << BigInt(7 * i)
  }
  return value
}


function getValue(mode: number, buffer: Uint8Array, startIndex: number) {
  switch (mode) {
    case kTypeVarInt:
      for (let i = startIndex; i < buffer.length; i++) {
        if (!(buffer[i] & 0b10000000)) {
          return {
            value: buffer.subarray(startIndex, i + 1),
            offset: 0
          }
        }
      }
      return {
        value: buffer.subarray(startIndex),
        offset: 0
      }
    case kTypeLengthDelim: {
      const offset = countNumberBytes(buffer, startIndex)
      const size = decodeNumber(buffer, startIndex)
      return {
        value: buffer.subarray(startIndex + offset, startIndex + offset + Number(size)),
        offset
      }
    }
    default:
      throw new Error(`Unrecognized value type: ${mode}`)
  }
}

function lowBits(number: Numeric): number {
  return typeof number !== 'bigint'
    ? (number >>> 0) % lowMaxPlus1
    : Number(number & lowMaxBig)
}

function highBits(number: Numeric): number {
  return typeof number !== 'bigint'
    ? (number / lowMaxPlus1) >>> 0
    : Number(number >> 32n & lowMaxBig)
}

function long(number: Numeric): Array<number> {
  const sign = number < 0
  if (sign) number = -number

  let lo = lowBits(number)
  let hi = highBits(number)

  if (sign) {
    hi = ~hi >>> 0
    lo = ~lo >>> 0
    if (++lo > lowMax) {
      lo = 0
      if (++hi > lowMax) { hi = 0 }
    }
  }

  return [hi, lo]
}

/**
 * Public helpers. These are used in the type definitions.
 */
const kTypeVarInt = 0
const kTypeLengthDelim = 2

function decodeNumber(buffer: Uint8Array, start = 0): Numeric {
  if (start >= buffer.length) return 0

  // Unrolled varint decoding for common small values
  const x = buffer[start]
  if (x < 0x80) return x

  if (start + 1 >= buffer.length) return x & 0x7f
  const y = buffer[start + 1]
  if (y < 0x80) return (x & 0x7f) | (y << 7)

  // Fallback to general case for 3+ bytes
  const size = countNumberBytes(buffer, start)
  if (size > 4) return decodeBigNumber(buffer.subarray(start))

  let value = (x & 0x7f) | ((y & 0x7f) << 7)
  let shift = 14
  for (let i = start + 2; i < start + size; i++) {
    value |= (buffer[i] & 0x7f) << shift
    shift += 7
  }
  return value
}


// Number.MAX_SAFE_INTEGER as BigInt.
const MAX_SAFE = 9007199254740991n; 

function decodeNumbers(buffer: Uint8Array, start = 0, end = buffer.length): Array<Numeric> {
  if (end === 0) return [];

  // Pre-allocation guess, capped at 8MB, to reduce array growth overhead.
  const out: Array<Numeric> = new Array(Math.min(end - start, 8388608)); 

  let o = 0; // write index
  let i = start; // read cursor
  const buf = buffer; // local alias for JIT

  const bulkEnd = end - 3;
  while (i < end) {
      const b0 = buf[i++];

    if (i < bulkEnd) {
      // Fast check: if all are single-byte varints.
      const b1=buf[i], b2=buf[i+1], b3=buf[i+2]
      if ((b0 | b1 | b2 | b3) < 0x80) {
        out[o++] = b0; out[o++] = b1; out[o++] = b2; out[o++] = b3
        i += 3
        continue
      }
      // Also check for 2 consecutive 2-byte varints (cont,final,cont,final)
      if (b0 >= 0x80 && b1 < 0x80 && b2 >= 0x80 && b3 < 0x80) {
        out[o++] = (b0 & 0x7f) | (b1 << 7)
        out[o++] = (b2 & 0x7f) | (b3 << 7)
        i += 3
        continue
      }
    }

    // Unrolled single varint decoding, for 1, 2, 3 and 4 byte varints.
    if (b0 < 0x80) { out[o++] = b0; continue; }

    if (i >= end) { out[o++] = (b0 & 0x7f); break; }
    const b1 = buf[i++];
    let v = (b0 & 0x7f) | ((b1 & 0x7f) << 7);
    if (b1 < 0x80) { out[o++] = v; continue; }

    if (i >= end) { out[o++] = v; break; }
    const b2 = buf[i++];
    v |= (b2 & 0x7f) << 14;
    if (b2 < 0x80) { out[o++] = v; continue; }

    if (i >= end) { out[o++] = v; break; }
    const b3 = buf[i++];
    v |= (b3 & 0x7f) << 21;
    if (b3 < 0x80) { out[o++] = v; continue; }

    // 5+ bytes: assemble as BigInt with multiplication.
    let big = BigInt(v);
    let mul = 1n << 28n; // 128^4 = 2^(7*4) since we've consumed 4 continuation chunks

    // We've consumed 4 bytes already; read up to protobuf's max of 10 total.
    for (let bytesRead = 0; bytesRead < 6; bytesRead++) {
      if (i >= end) { out[o++] = big; i = end; break; }
      const bx = buf[i++];
      big += BigInt(bx & 0x7f) * mul;
      if (bx < 0x80) {
        // Downcast when safe to match legacy behavior.
        out[o++] = (big <= MAX_SAFE) ? Number(big) : big;
        break;
      }
      mul *= 128n;
      if (bytesRead === 5) {
        // Malformed (continuation past 10th byte). Emit partial to advance.
        out[o++] = (big <= MAX_SAFE) ? Number(big) : big;
      }
    }
  }

  // Trim out to actual size.
  out.length = o; 
  return out;
}

function push<T>(value: T, list?: Array<T>): Array<T> {
  if (list == null) {
    return [value]
  }
  list.push(value)
  return list
}

function measureNumber(number: Numeric): number {
  if (number === 0 || number === 0n) return 0
  const [hi, lo] = long(number)

  const a = lo
  const b = (lo >>> 28 | hi << 4) >>> 0
  const c = hi >>> 24

  if (c !== 0) {
    return c < 128 ? 9 : 10
  }

  if (b !== 0) {
    if (b < 16384) {
      return b < 128 ? 5 : 6
    }

    return b < 2097152 ? 7 : 8
  }

  if (a < 16384) {
    return a < 128 ? 1 : 2
  }

  return a < 2097152 ? 3 : 4
}

function measureValue<T>(value: T): number {
  if (typeof value === 'undefined') return 0
  if (typeof value === 'number' || typeof value === 'bigint') {
    return measureNumber(value) || 1
  }
  return (value as Array<T>).length
}

function measureArray<T>(list: Array<T>): number {
  let size = 0
  for (const item of list) {
    size += measureValue(item)
  }
  return size
}

function measureNumberField(number: Numeric): number {
  const length = measureNumber(number)
  return length ? 1 + length : 0
}

function measureNumberArrayField(values: Numeric[]): number {
  let total = 0
  for (const value of values) {
    // Arrays should always include zeros to keep positions consistent
    total += measureNumber(value) || 1
  }
  // Packed arrays are encoded as Tag,Len,ConcatenatedElements
  // Tag is only one byte because field number is always < 16 in pprof
  return total ? 1 + measureNumber(total) + total : 0
}

function measureLengthDelimField<T>(value: T): number {
  const length = measureValue(value)
  // Length delimited records / submessages are encoded as Tag,Len,EncodedRecord
  // Tag is only one byte because field number is always < 16 in pprof
  return length ? 1 + measureNumber(length) + length : 0
}

function measureLengthDelimArrayField<T>(values: T[]): number {
  let total = 0
  for (const value of values) {
    total += measureLengthDelimField(value)
  }
  return total
}

function encodeNumber(buffer: Uint8Array, i: number, number: Numeric): number {
  if (number === 0 || number === 0n) {
    buffer[i++] = 0
    return i
  }

  let [hi, lo] = long(number)

  while (hi) {
    buffer[i++] = lo & 127 | 128
    lo = (lo >>> 7 | hi << 25) >>> 0
    hi >>>= 7
  }
  while (lo > 127) {
    buffer[i++] = lo & 127 | 128
    lo = lo >>> 7
  }
  buffer[i++] = lo

  return i
}

export const emptyTableToken = Symbol()

export class StringTable {
  strings = new Array<string>()
  #encodings = new Array<Uint8Array>()
  #positions = new Map<string, number>()

  constructor(tok?: typeof emptyTableToken) {
    if (tok !== emptyTableToken) {
      this.dedup('')
    }
  }

  get encodedLength(): number {
    let size = 0
    for (const encoded of this.#encodings) {
      size += encoded.length
    }
    return size
  }

  _encodeToBuffer(buffer: Uint8Array, offset: number): number {
    for (const encoded of this.#encodings) {
      buffer.set(encoded, offset)
      offset += encoded.length
    }
    return offset
  }

  encode(buffer = new Uint8Array(this.encodedLength)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  static _encodeStringFromUtf8(stringBuffer: Uint8Array | Buffer): Uint8Array {
    const buffer = new Uint8Array(1 + stringBuffer.length + (measureNumber(stringBuffer.length) || 1))
    let offset = 0
    buffer[offset++] = 50 // (6 << 3) + kTypeLengthDelim
    offset = encodeNumber(buffer, offset, stringBuffer.length)
    if (stringBuffer.length > 0) {
      buffer.set(stringBuffer, offset++)
    }
    return buffer
  }

  static _encodeString(string: string): Uint8Array {
    return StringTable._encodeStringFromUtf8(toUtf8(string))
  }

  dedup(string: string): number {
    if (typeof string === 'number') return string
    if (!this.#positions.has(string)) {
      const pos = this.strings.push(string) - 1
      this.#positions.set(string, pos)

      // Encode strings on insertion
      this.#encodings.push(StringTable._encodeString(string))
    }
    return this.#positions.get(string)
  }

  _decodeString(buffer: Uint8Array) {
    const string = new TextDecoder().decode(buffer)
    this.#positions.set(string, this.strings.push(string) - 1)
    this.#encodings.push(StringTable._encodeStringFromUtf8(buffer))
  }
}

function decode<T>(
  buffer: Uint8Array,
  decoder: (data: DeepPartial<T>, field: number, value: Uint8Array) => void
): DeepPartial<T> {
  const data = {}
  let index = 0

  while (index < buffer.length) {
    const field = buffer[index] >> 3
    const mode = buffer[index] & 0b111
    index++

    const { offset, value } = getValue(mode, buffer, index)
    index += value.length + offset

    decoder(data, field, value)
  }

  return data
}

export type ValueTypeInput = {
  type?: Numeric
  unit?: Numeric
}

export class ValueType {
  type: Numeric
  unit: Numeric

  static create(data: ValueTypeInput): ValueType {
    return data instanceof ValueType ? data : new ValueType(data)
  }

  constructor(data: ValueTypeInput) {
    this.type = data.type || 0
    this.unit = data.unit || 0
  }

  get length() {
    let total = 0
    total += measureNumberField(this.type)
    total += measureNumberField(this.unit)
    return total
  }

  _encodeToBuffer(buffer: Uint8Array, offset = 0): number {
    if (this.type) {
      buffer[offset++] = 8 // (1 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.type)
    }

    if (this.unit) {
      buffer[offset++] = 16 // (2 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.unit)
    }

    return offset
  }

  encode(buffer = new Uint8Array(this.length)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  static decodeValue(data: ValueTypeInput, field: number, buffer: Uint8Array) {
    switch (field) {
      case 1:
        data.type = decodeNumber(buffer)
        break
      case 2:
        data.unit = decodeNumber(buffer)
        break
    }
  }

  static decode(buffer: Uint8Array): ValueType {
    return new this(decode(buffer, this.decodeValue) as ValueTypeInput)
  }
}

export type LabelInput = {
  key?: Numeric
  str?: Numeric
  num?: Numeric
  numUnit?: Numeric
}

export class Label {
  key: Numeric
  str: Numeric
  num: Numeric
  numUnit: Numeric

  static create(data: LabelInput): Label {
    return data instanceof Label ? data : new Label(data)
  }

  constructor(data: LabelInput) {
    this.key = data.key || 0
    this.str = data.str || 0
    this.num = data.num || 0
    this.numUnit = data.numUnit || 0
  }

  get length() {
    let total = 0
    total += measureNumberField(this.key)
    total += measureNumberField(this.str)
    total += measureNumberField(this.num)
    total += measureNumberField(this.numUnit)
    return total
  }

  _encodeToBuffer(buffer: Uint8Array, offset = 0): number {
    if (this.key) {
      buffer[offset++] = 8 // (1 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.key)
    }

    if (this.str) {
      buffer[offset++] = 16 // (2 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.str)
    }

    if (this.num) {
      buffer[offset++] = 24 // (3 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.num)
    }

    if (this.numUnit) {
      buffer[offset++] = 32 // (4 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.numUnit)
    }

    return offset
  }

  encode(buffer = new Uint8Array(this.length)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  static decodeValue(data: LabelInput, field: number, buffer: Uint8Array) {
    switch (field) {
      case 1:
        data.key = decodeNumber(buffer)
        break
      case 2:
        data.str = decodeNumber(buffer)
        break
      case 3:
        data.num = decodeNumber(buffer)
        break
      case 4:
        data.numUnit = decodeNumber(buffer)
        break
    }
  }

  static decode(buffer: Uint8Array): Label {
    return new this(decode(buffer, this.decodeValue) as LabelInput)
  }
}

export type SampleInput = {
  locationId?: Array<Numeric>
  value?: Array<Numeric>
  label?: Array<LabelInput>
}

export class Sample {
  locationId: Array<Numeric>
  value: Array<Numeric>
  label: Array<Label>

  static create(data: SampleInput): Sample {
    return data instanceof Sample ? data : new Sample(data)
  }

  constructor(data: SampleInput) {
    this.locationId = data.locationId || []
    this.value = data.value || []
    this.label = (data.label || []).map(Label.create)
  }

  get length() {
    let total = 0
    total += measureNumberArrayField(this.locationId)
    total += measureNumberArrayField(this.value)
    total += measureLengthDelimArrayField(this.label)
    return total
  }

  _encodeToBuffer(buffer: Uint8Array, offset = 0): number {
    if (this.locationId.length) {
      buffer[offset++] = 10 // (1 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, measureArray(this.locationId))
      for (const locationId of this.locationId) {
        offset = encodeNumber(buffer, offset, locationId)
      }
    }

    if (this.value.length) {
      buffer[offset++] = 18 // (2 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, measureArray(this.value))
      for (const value of this.value) {
        offset = encodeNumber(buffer, offset, value)
      }
    }

    for (const label of this.label) {
      buffer[offset++] = 26 // (3 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, label.length)
      offset = label._encodeToBuffer(buffer, offset)
    }

    return offset
  }

  encode(buffer = new Uint8Array(this.length)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  static decode(buffer: Uint8Array): Sample {
    const out = {} as SampleInput;
    let index = 0

    // Inline `decode` and `getValue` to avoid re-slicing buf, and just pass
    // offsets to decodeNumbers instead.
    while (index < buffer.length) {
      const field = buffer[index] >> 3
      const mode = buffer[index] & 0b111
      index++

      if (mode === kTypeVarInt) {
        let end = index;
        while (end < buffer.length && buffer[end] >= 0x80) end++;
        end++; // include final byte

        switch (field) {
        case 1:
          out.locationId = decodeNumbers(buffer, index, end)
          break
        case 2:
          out.value = decodeNumbers(buffer, index, end)
          break
        }
        index = end
      } else if (mode === kTypeLengthDelim) {
        // Read length varint first
        let len = 0
        let shift = 0

        while (index < buffer.length) {
          const b = buffer[index++]
          len |= (b & 0x7f) << shift
          if (b < 0x80) break
          shift += 7
        }

        const dataStart = index
        const dataEnd = index + len

        switch (field) {
        case 1:
          out.locationId = decodeNumbers(buffer, dataStart, dataEnd)
          break
        case 2:
          out.value = decodeNumbers(buffer, dataStart, dataEnd)
          break
        case 3:
          out.label = push(Label.decode(buffer.subarray(dataStart, dataEnd)), out.label)
          break
        }
        index = dataEnd
      } else {
        throw new Error(`Unrecognized value type: ${mode}`)
      }
    }

    return new this(out);
  }
}

export type MappingInput = {
  id?: Numeric
  memoryStart?: Numeric
  memoryLimit?: Numeric
  fileOffset?: Numeric
  filename?: Numeric
  buildId?: Numeric
  hasFunctions?: boolean
  hasFilenames?: boolean
  hasLineNumbers?: boolean
  hasInlineFrames?: boolean
}

export class Mapping {
  id: Numeric
  memoryStart: Numeric
  memoryLimit: Numeric
  fileOffset: Numeric
  filename: Numeric
  buildId: Numeric
  hasFunctions: boolean
  hasFilenames: boolean
  hasLineNumbers: boolean
  hasInlineFrames: boolean

  static create(data: MappingInput): Mapping {
    return data instanceof Mapping ? data : new Mapping(data)
  }

  constructor(data: MappingInput) {
    this.id = data.id || 0
    this.memoryStart = data.memoryStart || 0
    this.memoryLimit = data.memoryLimit || 0
    this.fileOffset = data.fileOffset || 0
    this.filename = data.filename || 0
    this.buildId = data.buildId || 0
    this.hasFunctions = !!data.hasFunctions
    this.hasFilenames = !!data.hasFilenames
    this.hasLineNumbers = !!data.hasLineNumbers
    this.hasInlineFrames = !!data.hasInlineFrames
  }

  get length() {
    let total = 0
    total += measureNumberField(this.id)
    total += measureNumberField(this.memoryStart)
    total += measureNumberField(this.memoryLimit)
    total += measureNumberField(this.fileOffset)
    total += measureNumberField(this.filename)
    total += measureNumberField(this.buildId)
    total += measureNumberField(this.hasFunctions ? 1 : 0)
    total += measureNumberField(this.hasFilenames ? 1 : 0)
    total += measureNumberField(this.hasLineNumbers ? 1 : 0)
    total += measureNumberField(this.hasInlineFrames ? 1 : 0)
    return total
  }

  _encodeToBuffer(buffer: Uint8Array, offset = 0): number {
    if (this.id) {
      buffer[offset++] = 8 // (1 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.id)
    }
    if (this.memoryStart) {
      buffer[offset++] = 16 // (2 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.memoryStart)
    }
    if (this.memoryLimit) {
      buffer[offset++] = 24 // (3 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.memoryLimit)
    }
    if (this.fileOffset) {
      buffer[offset++] = 32 // (4 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.fileOffset)
    }
    if (this.filename) {
      buffer[offset++] = 40 // (5 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.filename)
    }
    if (this.buildId) {
      buffer[offset++] = 48 // (6 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.buildId)
    }
    if (this.hasFunctions) {
      buffer[offset++] = 56 // (7 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, 1)
    }
    if (this.hasFilenames) {
      buffer[offset++] = 64 // (8 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, 1)
    }
    if (this.hasLineNumbers) {
      buffer[offset++] = 72 // (9 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, 1)
    }
    if (this.hasInlineFrames) {
      buffer[offset++] = 80 // (10 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, 1)
    }
    return offset
  }

  encode(buffer = new Uint8Array(this.length)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  static decodeValue(data: MappingInput, field: number, buffer: Uint8Array) {
    switch (field) {
      case 1:
        data.id = decodeNumber(buffer)
        break
      case 2:
        data.memoryStart = decodeNumber(buffer)
        break
      case 3:
        data.memoryLimit = decodeNumber(buffer)
        break
      case 4:
        data.fileOffset = decodeNumber(buffer)
        break
      case 5:
        data.filename = decodeNumber(buffer)
        break
      case 6:
        data.buildId = decodeNumber(buffer)
        break
      case 7:
        data.hasFunctions = !!decodeNumber(buffer)
        break
      case 8:
        data.hasFilenames = !!decodeNumber(buffer)
        break
      case 9:
        data.hasLineNumbers = !!decodeNumber(buffer)
        break
      case 10:
        data.hasInlineFrames = !!decodeNumber(buffer)
        break
    }
  }

  static decode(buffer: Uint8Array): Mapping {
    return new this(decode(buffer, this.decodeValue) as MappingInput)
  }
}

export type LineInput = {
  functionId?: Numeric
  line?: Numeric
}

export class Line {
  functionId: Numeric
  line: Numeric

  static create(data: LineInput): Line {
    return data instanceof Line ? data : new Line(data)
  }

  constructor(data: LineInput) {
    this.functionId = data.functionId || 0
    this.line = data.line || 0
  }

  get length() {
    let total = 0
    total += measureNumberField(this.functionId)
    total += measureNumberField(this.line)
    return total
  }

  _encodeToBuffer(buffer: Uint8Array, offset = 0): number {
    if (this.functionId) {
      buffer[offset++] = 8 // (1 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.functionId)
    }

    if (this.line) {
      buffer[offset++] = 16 // (2 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.line)
    }

    return offset
  }

  encode(buffer = new Uint8Array(this.length)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  static decodeValue(data: LineInput, field: number, buffer: Uint8Array) {
    switch (field) {
      case 1:
        data.functionId = decodeNumber(buffer)
        break
      case 2:
        data.line = decodeNumber(buffer)
        break
    }
  }

  static decode(buffer: Uint8Array): Line {
    return new this(decode(buffer, this.decodeValue) as LineInput)
  }
}

export type LocationInput = {
  id?: Numeric
  mappingId?: Numeric
  address?: Numeric
  line?: Array<LineInput>
  isFolded?: boolean
}

export class Location {
  id: Numeric
  mappingId: Numeric
  address: Numeric
  line: Array<Line>
  isFolded: boolean

  static create(data: LocationInput): Location {
    return data instanceof Location ? data : new Location(data)
  }

  constructor(data: LocationInput) {
    this.id = data.id || 0
    this.mappingId = data.mappingId || 0
    this.address = data.address || 0
    this.line = (data.line || []).map(Line.create)
    this.isFolded = !!data.isFolded
  }

  get length() {
    let total = 0
    total += measureNumberField(this.id)
    total += measureNumberField(this.mappingId)
    total += measureNumberField(this.address)
    total += measureLengthDelimArrayField(this.line)
    total += measureNumberField(this.isFolded ? 1 : 0)
    return total
  }

  _encodeToBuffer(buffer: Uint8Array, offset = 0): number {
    if (this.id) {
      buffer[offset++] = 8 // (1 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.id)
    }
    if (this.mappingId) {
      buffer[offset++] = 16 // (2 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.mappingId)
    }
    if (this.address) {
      buffer[offset++] = 24 // (3 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.address)
    }
    for (const line of this.line) {
      buffer[offset++] = 34 // (4 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, line.length)
      offset = line._encodeToBuffer(buffer, offset)
    }
    if (this.isFolded) {
      buffer[offset++] = 40 // (5 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, 1)
    }

    return offset
  }

  encode(buffer = new Uint8Array(this.length)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  static decodeValue(data: LocationInput, field: number, buffer: Uint8Array) {
    switch (field) {
      case 1:
        data.id = decodeNumber(buffer)
        break
      case 2:
        data.mappingId = decodeNumber(buffer)
        break
      case 3:
        data.address = decodeNumber(buffer)
        break
      case 4:
        data.line = push(Line.decode(buffer), data.line)
        break
      case 5:
        data.isFolded = !!decodeNumber(buffer)
        break
    }
  }

  static decode(buffer: Uint8Array): Location {
    return new this(decode(buffer, this.decodeValue) as LocationInput)
  }
}

export type FunctionInput = {
  id?: Numeric
  name?: Numeric
  systemName?: Numeric
  filename?: Numeric
  startLine?: Numeric
}

export class Function {
  id: Numeric
  name: Numeric
  systemName: Numeric
  filename: Numeric
  startLine: Numeric

  static create(data: FunctionInput): Function {
    return data instanceof Function ? data : new Function(data)
  }

  constructor(data: FunctionInput) {
    this.id = data.id || 0
    this.name = data.name || 0
    this.systemName = data.systemName || 0
    this.filename = data.filename || 0
    this.startLine = data.startLine || 0
  }

  get length() {
    let total = 0
    total += measureNumberField(this.id)
    total += measureNumberField(this.name)
    total += measureNumberField(this.systemName)
    total += measureNumberField(this.filename)
    total += measureNumberField(this.startLine)
    return total
  }

  _encodeToBuffer(buffer: Uint8Array, offset = 0): number {
    if (this.id) {
      buffer[offset++] = 8 // (1 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.id)
    }
    if (this.name) {
      buffer[offset++] = 16 // (2 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.name)
    }
    if (this.systemName) {
      buffer[offset++] = 24 // (3 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.systemName)
    }
    if (this.filename) {
      buffer[offset++] = 32 // (4 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.filename)
    }
    if (this.startLine) {
      buffer[offset++] = 40 // (5 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.startLine)
    }

    return offset
  }

  encode(buffer = new Uint8Array(this.length)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  static decodeValue(data: FunctionInput, field: number, buffer: Uint8Array) {
    switch (field) {
      case 1:
        data.id = decodeNumber(buffer)
        break
      case 2:
        data.name = decodeNumber(buffer)
        break
      case 3:
        data.systemName = decodeNumber(buffer)
        break
      case 4:
        data.filename = decodeNumber(buffer)
        break
      case 5:
        data.startLine = decodeNumber(buffer)
        break
    }
  }

  static decode(buffer: Uint8Array): Function {
    return new this(decode(buffer, this.decodeValue) as FunctionInput)
  }
}

export type ProfileInput = {
  sampleType?: Array<ValueTypeInput>
  sample?: Array<SampleInput>
  mapping?: Array<MappingInput>
  location?: Array<LocationInput>
  function?: Array<FunctionInput>
  stringTable?: StringTable
  dropFrames?: Numeric
  keepFrames?: Numeric
  timeNanos?: Numeric
  durationNanos?: Numeric
  periodType?: ValueTypeInput
  period?: Numeric
  comment?: Array<Numeric>
  defaultSampleType?: Numeric
}

export class Profile {
  sampleType: Array<ValueType>
  sample: Array<Sample>
  mapping: Array<Mapping>
  location: Array<Location>
  function: Array<Function>
  stringTable: StringTable
  dropFrames: Numeric
  keepFrames: Numeric
  timeNanos: Numeric
  durationNanos: Numeric
  periodType?: ValueType
  period: Numeric
  comment: Array<Numeric>
  defaultSampleType: Numeric

  constructor(data: ProfileInput = {}) {
    this.sampleType = (data.sampleType || []).map(ValueType.create)
    this.sample = (data.sample || []).map(Sample.create)
    this.mapping = (data.mapping || []).map(Mapping.create)
    this.location = (data.location || []).map(Location.create)
    this.function = (data.function || []).map(Function.create)
    this.stringTable = data.stringTable || new StringTable()
    this.dropFrames = data.dropFrames || 0
    this.keepFrames = data.keepFrames || 0
    this.timeNanos = data.timeNanos || 0
    this.durationNanos = data.durationNanos || 0
    this.periodType = data.periodType ? ValueType.create(data.periodType) : undefined
    this.period = data.period || 0
    this.comment = data.comment || []
    this.defaultSampleType = data.defaultSampleType || 0
  }

  get length() {
    let total = 0
    total += measureLengthDelimArrayField(this.sampleType)
    total += measureLengthDelimArrayField(this.sample)
    total += measureLengthDelimArrayField(this.mapping)
    total += measureLengthDelimArrayField(this.location)
    total += measureLengthDelimArrayField(this.function)
    total += this.stringTable.encodedLength
    total += measureNumberField(this.dropFrames)
    total += measureNumberField(this.keepFrames)
    total += measureNumberField(this.timeNanos)
    total += measureNumberField(this.durationNanos)
    total += measureLengthDelimField(this.periodType)
    total += measureNumberField(this.period)
    total += measureNumberArrayField(this.comment)
    total += measureNumberField(this.defaultSampleType)
    return total
  }

  _encodeSampleTypesToBuffer(buffer: Uint8Array, offset = 0): number {
    for (const sampleType of this.sampleType) {
      buffer[offset++] = 10 // (1 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, sampleType.length)
      offset = sampleType._encodeToBuffer(buffer, offset)
    }
    return offset
  }

  _encodeSamplesToBuffer(buffer: Uint8Array, offset = 0): number {
    for (const sample of this.sample) {
      buffer[offset++] = 18 // (2 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, sample.length)
      offset = sample._encodeToBuffer(buffer, offset)
    }
    return offset
  }

  _encodeMappingsToBuffer(buffer: Uint8Array, offset = 0): number {
    for (const mapping of this.mapping) {
      buffer[offset++] = 26 // (3 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, mapping.length)
      offset = mapping._encodeToBuffer(buffer, offset)
    }
    return offset
  }

  _encodeLocationsToBuffer(buffer: Uint8Array, offset = 0): number {
    for (const location of this.location) {
      buffer[offset++] = 34 // (4 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, location.length)
      offset = location._encodeToBuffer(buffer, offset)
    }
    return offset
  }

  _encodeFunctionsToBuffer(buffer: Uint8Array, offset = 0): number {
    for (const fun of this.function) {
      buffer[offset++] = 42 // (5 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, fun.length)
      offset = fun._encodeToBuffer(buffer, offset)
    }
    return offset
  }

  _encodeBasicValuesToBuffer(buffer: Uint8Array, offset = 0): number {
    if (this.dropFrames) {
      buffer[offset++] = 56 // (7 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.dropFrames)
    }

    if (this.keepFrames) {
      buffer[offset++] = 64 // (8 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.keepFrames)
    }

    if (this.timeNanos) {
      buffer[offset++] = 72 // (9 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.timeNanos)
    }

    if (this.durationNanos) {
      buffer[offset++] = 80 // (10 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.durationNanos)
    }

    if (typeof this.periodType !== 'undefined') {
      buffer[offset++] = 90 // (11 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, this.periodType.length)
      offset = this.periodType._encodeToBuffer(buffer, offset)
    }

    if (this.period) {
      buffer[offset++] = 96 // (12 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.period)
    }

    if (this.comment.length) {
      buffer[offset++] = 106 // (13 << 3) + kTypeLengthDelim
      offset = encodeNumber(buffer, offset, measureArray(this.comment))
      for (const comment of this.comment) {
        offset = encodeNumber(buffer, offset, comment)
      }
    }

    if (this.defaultSampleType) {
      buffer[offset++] = 112 // (14 << 3) + kTypeVarInt
      offset = encodeNumber(buffer, offset, this.defaultSampleType)
    }

    return offset
  }

  _encodeToBuffer(buffer: Uint8Array, offset = 0): number {
    offset = this._encodeSampleTypesToBuffer(buffer, offset)
    offset = this._encodeSamplesToBuffer(buffer, offset)
    offset = this._encodeMappingsToBuffer(buffer, offset)
    offset = this._encodeLocationsToBuffer(buffer, offset)
    offset = this._encodeFunctionsToBuffer(buffer, offset)
    offset = this.stringTable._encodeToBuffer(buffer, offset)
    offset = this._encodeBasicValuesToBuffer(buffer, offset)
    return offset
  }

  async _encodeToBufferAsync(buffer: Uint8Array, offset = 0): Promise<number> {
    offset = this._encodeSampleTypesToBuffer(buffer, offset)
    await new Promise(setImmediate)

    offset = this._encodeSamplesToBuffer(buffer, offset)
    await new Promise(setImmediate)

    offset = this._encodeMappingsToBuffer(buffer, offset)
    await new Promise(setImmediate)

    offset = this._encodeLocationsToBuffer(buffer, offset)
    await new Promise(setImmediate)

    offset = this._encodeFunctionsToBuffer(buffer, offset)
    await new Promise(setImmediate)

    offset = this.stringTable._encodeToBuffer(buffer, offset)
    await new Promise(setImmediate)

    offset = this._encodeBasicValuesToBuffer(buffer, offset)
    return offset
  }

  encode(buffer = new Uint8Array(this.length)): Uint8Array {
    this._encodeToBuffer(buffer, 0)
    return buffer
  }

  async encodeAsync(buffer = new Uint8Array(this.length)): Promise<Uint8Array> {
    await this._encodeToBufferAsync(buffer, 0)
    return buffer
  }

  static decodeValue(data: ProfileInput, field: number, buffer: Uint8Array) {
    switch (field) {
      case 1:
        data.sampleType = push(ValueType.decode(buffer), data.sampleType)
        break
      case 2:
        data.sample = push(Sample.decode(buffer), data.sample)
        break
      case 3:
        data.mapping = push(Mapping.decode(buffer), data.mapping)
        break
      case 4:
        data.location = push(Location.decode(buffer), data.location)
        break
      case 5:
        data.function = push(Function.decode(buffer), data.function)
        break
      case 6: {
        if (data.stringTable === undefined) {
          data.stringTable = new StringTable(emptyTableToken)
        }
        data.stringTable._decodeString(buffer)
        break
      }
      case 7:
        data.dropFrames = decodeNumber(buffer)
        break
      case 8:
        data.keepFrames = decodeNumber(buffer)
        break
      case 9:
        data.timeNanos = decodeNumber(buffer)
        break
      case 10:
        data.durationNanos = decodeNumber(buffer)
        break
      case 11:
        data.periodType = ValueType.decode(buffer)
        break
      case 12:
        data.period = decodeNumber(buffer)
        break
      case 13:
        data.comment = decodeNumbers(buffer)
        break
      case 14:
        data.defaultSampleType = decodeNumber(buffer)
        break
    }
  }

  static decode(buffer: Uint8Array): Profile {
    return new this(decode(buffer, this.decodeValue) as ProfileInput)
  }
}
