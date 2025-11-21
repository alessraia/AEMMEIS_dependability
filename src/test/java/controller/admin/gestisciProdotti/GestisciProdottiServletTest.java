package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Autore;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;

/**
 * Unit tests for GestisciProdottiServlet.
 * Tests the servlet's ability to retrieve all books and forward them to the products management page.
 */
class GestisciProdottiServletTest {

    private GestisciProdottiServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new GestisciProdottiServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/gestisciProdotti.jsp"))
                .thenReturn(dispatcher);
    }

    /**
     * Helper method to create a Libro object with single author.
     */
    private Libro createLibro(String isbn, String title, String autoreName) {
        Libro libro = new Libro();
        libro.setIsbn(isbn);
        libro.setTitolo(title);
        
        // Libro has a List<Autore>, so we create a list with one author
        List<Autore> autori = new ArrayList<>();
        if (autoreName != null) {
            Autore autore = new Autore();
            autore.setNome(autoreName);
            autori.add(autore);
        }
        libro.setAutori(autori);
        
        return libro;
    }

    /**
     * Test basic functionality: retrieve books and forward to JSP.
     * Scenario: doGet retrieves all books and forwards to gestisciProdotti.jsp
     */
    @Test
    void testDoGet_BasicRetrievalAndForward() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-1234567890", "Book1", "Author1"));
        libri.add(createLibro("978-0987654321", "Book2", "Author2"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("libri", libri);
            verify(request).getRequestDispatcher("/WEB-INF/results/admin/prodotti/gestisciProdotti.jsp");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test empty book list.
     * Scenario: No books available, empty list is returned
     */
    @Test
    void testDoGet_EmptyBookList() throws ServletException, IOException {
        // Arrange
        List<Libro> emptyList = new ArrayList<>();

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(emptyList);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("libri", emptyList);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test single book retrieval.
     * Scenario: Only one book is available
     */
    @Test
    void testDoGet_SingleBook() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-1111111111", "SingleBook", "SingleAuthor"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("libri", libri);
            assert libri.size() == 1;
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test large book collection.
     * Scenario: Many books are retrieved
     */
    @Test
    void testDoGet_LargeBookCollection() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        for (int i = 0; i < 100; i++) {
            libri.add(createLibro("978-" + String.format("%010d", i), "Book" + i, "Author" + i));
        }

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("libri", libri);
            assert libri.size() == 100;
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test DAO instantiation and method call.
     * Scenario: LibroDAO is properly instantiated and doRetriveAll is called
     */
    @Test
    void testDoGet_DAOInstantiationAndCall() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-2222222222", "TestBook", "TestAuthor"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify DAO was instantiated and method was called
            assert mockedConstruction.constructed().size() == 1;
            LibroDAO dao = mockedConstruction.constructed().get(0);
            verify(dao).doRetriveAll();
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test request attribute setting.
     * Scenario: Returned list is properly set as request attribute with key "libri"
     */
    @Test
    void testDoGet_AttributeSettingWithCorrectKey() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-3333333333", "Book", "Author"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify setAttribute is called with correct key and value
            verify(request).setAttribute("libri", libri);
            verify(request).getRequestDispatcher("/WEB-INF/results/admin/prodotti/gestisciProdotti.jsp");
        }
    }

    /**
     * Test correct JSP forwarding path.
     * Scenario: Request is forwarded to correct JSP file
     */
    @Test
    void testDoGet_CorrectJSPPath() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify correct JSP path
            verify(request).getRequestDispatcher("/WEB-INF/results/admin/prodotti/gestisciProdotti.jsp");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    /**
     * Test dispatcher forward is called exactly once.
     * Scenario: Forward method is called once per request
     */
    @Test
    void testDoGet_DispatcherForwardCalledOnce() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-4444444444", "Book", "Author"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Forward called exactly once
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    /**
     * Test books with null fields.
     * Scenario: Books with null title or empty author list are handled
     */
    @Test
    void testDoGet_BooksWithNullFields() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        Libro libro1 = new Libro();
        libro1.setIsbn("978-5555555555");
        libro1.setTitolo(null);
        libro1.setAutori(new ArrayList<>()); // Empty author list
        libri.add(libro1);

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("libri", libri);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test various ISBN formats in book list.
     * Scenario: Books with different ISBN formats are retrieved
     */
    @Test
    void testDoGet_VariousISBNFormats() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-1234567890", "Book1", "Author1"));
        libri.add(createLibro("9781234567890", "Book2", "Author2"));
        libri.add(createLibro("123-456-789", "Book3", "Author3"));
        libri.add(createLibro("ISBN-10", "Book4", "Author4"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("libri", libri);
            assert libri.size() == 4;
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test doPost delegates to doGet.
     * Scenario: POST requests are handled the same as GET requests
     */
    @Test
    void testDoPost_DelegatesToDoGet() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-6666666666", "Book", "Author"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doPost(request, response);

            // Assert - Verify same behavior as doGet
            verify(request).setAttribute("libri", libri);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test books with special characters in title and author.
     * Scenario: Books with special characters in fields are handled
     */
    @Test
    void testDoGet_BooksWithSpecialCharacters() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-7777777777", "Book@#$%^&*()", "Autore/Scrittore"));
        libri.add(createLibro("978-8888888888", "Libro-con-trattini", "Autore con spazi"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("libri", libri);
            assert libri.size() == 2;
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null list returned from DAO.
     * Scenario: DAO returns null instead of empty list (edge case)
     */
    @Test
    void testDoGet_NullListFromDAO() throws ServletException, IOException {
        // Arrange
        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(null);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Servlet handles null gracefully
            verify(request).setAttribute("libri", null);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test correct attribute key usage.
     * Scenario: Verify exact attribute key "libri" is used
     */
    @Test
    void testDoGet_ExactAttributeKey() throws ServletException, IOException {
        // Arrange
        List<Libro> libri = new ArrayList<>();
        libri.add(createLibro("978-9999999999", "Book", "Author"));

        try (MockedConstruction<LibroDAO> mockedConstruction = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetriveAll()).thenReturn(libri);
                })) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify exact key "libri" is used
            verify(request).setAttribute("libri", libri);
            verify(dispatcher).forward(request, response);
        }
    }
}
