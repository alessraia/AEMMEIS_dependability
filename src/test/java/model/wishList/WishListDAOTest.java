package model.wishList;

import model.ConPool;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedStatic;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class WishListDAOTest {

    private WishListDAO wishListDAO;
    private LibroDAO mockLibroDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;
    private MockedStatic<ConPool> mockedConPool;

    @BeforeEach
    void setUp() throws SQLException {
        mockLibroDAO = mock(LibroDAO.class);
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);

        mockedConPool = mockStatic(ConPool.class);
        mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);

        wishListDAO = new WishListDAO(mockLibroDAO);
    }

    @AfterEach
    void tearDown() {
        if (mockedConPool != null) {
            mockedConPool.close();
        }
    }

    // ==================== Helper Methods ====================

    private WishList createValidWishList() {
        WishList wishList = new WishList();
        wishList.setEmail("test@example.com");
        return wishList;
    }

    private Libro createMockLibro(String isbn, String titolo) {
        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo(titolo);
        libro.setGenere("Fiction");
        libro.setPrezzo(19.99);
        libro.setSconto(10);
        return libro;
    }

    // ==================== doSave Tests ====================

    @Test
    void testDoSave_Success() throws SQLException {
        // Arrange
        WishList wishList = createValidWishList();
        String isbn = "9781234567890";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        wishListDAO.doSave(wishList, isbn);

        // Assert
        verify(mockPreparedStatement).setString(1, "test@example.com");
        verify(mockPreparedStatement).setString(2, isbn);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDoSave_InsertError() throws SQLException {
        // Arrange
        WishList wishList = createValidWishList();
        String isbn = "9781234567890";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> wishListDAO.doSave(wishList, isbn));
        assertEquals("INSERT error.", exception.getMessage());
    }

    @Test
    void testDoSave_SQLException() throws SQLException {
        // Arrange
        WishList wishList = createValidWishList();
        String isbn = "9781234567890";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> wishListDAO.doSave(wishList, isbn));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetrieveByEmail Tests ====================

    @Test
    void testDoRetrieveByEmail_WithBooks() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String isbn1 = "9781234567890";
        String isbn2 = "9780987654321";

        Libro libro1 = createMockLibro(isbn1, "Book 1");
        Libro libro2 = createMockLibro(isbn2, "Book 2");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getString(1)).thenReturn(email);
        when(mockResultSet.getString(2)).thenReturn(isbn1, isbn2);

        when(mockLibroDAO.doRetrieveById(isbn1)).thenReturn(libro1);
        when(mockLibroDAO.doRetrieveById(isbn2)).thenReturn(libro2);

        // Act
        WishList result = wishListDAO.doRetrieveByEmail(email);

        // Assert
        assertNotNull(result);
        assertEquals(email, result.getEmail());
        assertNotNull(result.getLibri());
        assertEquals(2, result.getLibri().size());
        assertEquals("Book 1", result.getLibri().get(0).getTitolo());
        assertEquals("Book 2", result.getLibri().get(1).getTitolo());
        verify(mockPreparedStatement).setString(1, email);
        verify(mockLibroDAO).doRetrieveById(isbn1);
        verify(mockLibroDAO).doRetrieveById(isbn2);
    }

    @Test
    void testDoRetrieveByEmail_EmptyWishList() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        WishList result = wishListDAO.doRetrieveByEmail(email);

        // Assert
        assertNotNull(result);
        assertNotNull(result.getLibri());
        assertTrue(result.getLibri().isEmpty());
        verify(mockPreparedStatement).setString(1, email);
    }

    @Test
    void testDoRetrieveByEmail_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> wishListDAO.doRetrieveByEmail(email));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== deleteLibro Tests ====================

    @Test
    void testDeleteLibro_Success() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String isbn = "9781234567890";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        wishListDAO.deleteLibro(email, isbn);

        // Assert
        verify(mockPreparedStatement).setString(1, email);
        verify(mockPreparedStatement).setString(2, isbn);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteLibro_DeleteError() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String isbn = "9781234567890";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> wishListDAO.deleteLibro(email, isbn));
        assertEquals("DELETE error.", exception.getMessage());
    }

    @Test
    void testDeleteLibro_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String isbn = "9781234567890";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> wishListDAO.deleteLibro(email, isbn));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== deleteWishListByEmail Tests ====================

    @Test
    void testDeleteWishListByEmail_Success() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(3); // 3 items deleted

        // Act
        wishListDAO.deleteWishListByEmail(email);

        // Assert
        verify(mockPreparedStatement).setString(1, email);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteWishListByEmail_DeleteError() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> wishListDAO.deleteWishListByEmail(email));
        assertEquals("DELETE error.", exception.getMessage());
    }

    @Test
    void testDeleteWishListByEmail_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> wishListDAO.deleteWishListByEmail(email));
        assertTrue(exception.getCause() instanceof SQLException);
    }
}
