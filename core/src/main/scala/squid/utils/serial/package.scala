package squid.utils

package object serial {
  // adapted from https://gist.github.com/laughedelic/634f1a1e5333d58085603fcff317f6b4
  
  import java.io._
  import java.util.Base64
  import java.nio.charset.StandardCharsets.UTF_8
  
  def serialize(value: Any): String = {
    val stream: ByteArrayOutputStream = new ByteArrayOutputStream()
    val oos = new ObjectOutputStream(stream)
    oos.writeObject(value)
    oos.close
    new String(
      Base64.getEncoder().encode(stream.toByteArray),
      UTF_8
    )
  }
  
  def deserialize(str: String): Any = {
    val bytes = Base64.getDecoder().decode(str.getBytes(UTF_8))
    val ois = new ObjectInputStream(new ByteArrayInputStream(bytes))
    val value = ois.readObject
    ois.close
    value
  }
  
}
