package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;

import static org.mockito.Mockito.*;

/**
 * Unit tests for NonDisponibile servlet.
 * Tests the servlet's ability to mark books as unavailable (non-disponibile)
 * and update their availability status in the system.
 */
class NonDisponibileTest {

    private NonDisponibile servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new NonDisponibile();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);
    }

    /**
     * Helper method to create a Libro with ISBN and availability status.
     */
    private Libro createLibro(String isbn, boolean disponibile) {
        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setDisponibile(disponibile);
        return libro;
    }

    /**
     * Test basic functionality: mark book as unavailable.
     * Scenario: Book with valid ISBN is marked as non-disponibile and forwarded
     */
    @Test
    void testDoGet_BasicMarkUnavailable() throws ServletException, IOException {
        // Arrange
        String isbn = "978-1234567890";
        when(request.getParameter("isbn")).thenReturn(isbn);

        Libro libro = createLibro(isbn, true);
        assert libro.isDisponibile();

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Book is now unavailable and forwarded
            assert !libro.isDisponibile();
            verify(request).getRequestDispatcher("gestisci-prodotti");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test DAO operations: retrieve, update, and verify calls.
     * Scenario: LibroDAO.doRetrieveById and updateDisponibile are called with correct parameters
     */
    @Test
    void testDoGet_DAOUpdateCalled() throws ServletException, IOException {
        // Arrange
        String isbn = "978-1111111111";
        when(request.getParameter("isbn")).thenReturn(isbn);

        Libro libro = createLibro(isbn, true);

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify DAO operations and forwarding
            assert mockedConstruction.constructed().size() == 1;
            LibroDAO dao = mockedConstruction.constructed().get(0);
            verify(dao).doRetrieveById(isbn);
            verify(dao).updateDisponibile(libro);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test book already unavailable.
     * Scenario: Book that is already unavailable remains unavailable
     */
    @Test
    void testDoGet_AlreadyUnavailableBook() throws ServletException, IOException {
        // Arrange
        String isbn = "978-4444444444";
        when(request.getParameter("isbn")).thenReturn(isbn);

        Libro libro = createLibro(isbn, false);
        assert !libro.isDisponibile();

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Still unavailable
            assert !libro.isDisponibile();
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test various ISBN formats and edge cases.
     * Scenario: Different valid ISBN formats, special characters, empty, and long values are handled
     */
    @Test
    void testDoGet_VariousISBNFormats() throws ServletException, IOException {
        String[] testCases = {
            "978-1234567890",
            "9781234567890",
            "123-456-789",
            "ISBN-10",
            "ISBN-13-FORMAT",
            "ISBN-123/456-ABC",
            "",
            "978-1234567890-VERY-LONG-ISBN-STRING-WITH-MANY-CHARACTERS"
        };

        for (String isbn : testCases) {
            // Arrange
            reset(request, response, dispatcher);
            when(request.getParameter("isbn")).thenReturn(isbn);
            when(request.getRequestDispatcher("gestisci-prodotti")).thenReturn(dispatcher);

            Libro libro = createLibro(isbn, true);

            try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                    (mock, context) -> {
                        when(mock.doRetrieveById(isbn)).thenReturn(libro);
                    })) {

                // Act
                servlet.doGet(request, response);

                // Assert
                assert !libro.isDisponibile();
                verify(dispatcher).forward(request, response);
            }
        }
    }

    /**
     * Test multiple consecutive unavailability operations.
     * Scenario: Same book marked unavailable multiple times
     */
    @Test
    void testDoGet_MultipleConsecutiveOperations() throws ServletException, IOException {
        // Arrange
        String isbn = "978-5555555555";
        when(request.getParameter("isbn")).thenReturn(isbn);

        Libro libro = createLibro(isbn, true);

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                })) {

            // Act - First operation
            servlet.doGet(request, response);
            assert !libro.isDisponibile();

            // Act - Second operation
            servlet.doGet(request, response);
            assert !libro.isDisponibile();

            // Assert
            verify(dispatcher, times(2)).forward(request, response);
        }
    }

    /**
     * Test DAO update receives correct book object with final state verification.
     * Scenario: Updated libro object is passed to updateDisponibile with correct state
     */
    @Test
    void testDoGet_CorrectBookObjectPassed() throws ServletException, IOException {
        // Arrange
        String isbn = "978-1010101010";
        when(request.getParameter("isbn")).thenReturn(isbn);

        Libro libro = createLibro(isbn, true);

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(isbn)).thenReturn(libro);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify the exact libro object is passed to update with correct state
            assert !libro.isDisponibile();
            LibroDAO dao = mockedConstruction.constructed().get(0);
            verify(dao).updateDisponibile(libro);
        }
    }
}
